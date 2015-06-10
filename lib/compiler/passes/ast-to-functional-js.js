var arrays  = require("../../utils/arrays"),
    js      = require("../javascript");
    visitor = require("../visitor"),
    objects = require('../../utils/objects');

if (typeof window === 'undefined') {
  var fs = require('fs');
  function readSource(moduleName) {
    var fileName = __dirname + '/' + moduleName + '.js';
    return fs.readFileSync(fileName, 'utf8');
  }
}

function generateJavascript(ast, options) {
  var subexpressions = [];
  var subxIndexes = {};

  function buildCall(name, args) {
    var parts = [
      name,
    '('];
    var i;
    for (i = 0; i < args.length; i++) {
      if (i !== 0) {
        parts.push(',');
      }
      parts.push(args[i]);
    }
    parts.push(')');
    return parts.join('');
  }

  function makeClosure(expression) {
    var index;
    if (subxIndexes[expression]) {
      index = subxIndexes[expression];
    } else {
      index = subexpressions.length;
      subxIndexes[expression] = index;
      subexpressions.push(
        'function peg$sub' + index + '(peg$state) {\n' +
        '  return ' + expression + ';\n' +
        '}');
    }
    return 'peg$sub' + index;
  }

  function makeStdCall(name, expressions, nodes, context) {
    var args = ['peg$state'].concat(expressions);
    for (var i = 0; i < nodes.length; i++) {
      args.push(makeClosure(generate(nodes[i], context)));
    }
    return buildCall(name, args);
  }

  function makeActionClosureArgs(code, env) {
    var keys = objects.keys(env);
    return [
      'function (' + keys.join(', ') + ') {\n' +
        '    ' + code + '\n' +
      '  }',
      JSON.stringify(keys)];
  }

  var generate = visitor.build({
    grammar: function(node) {
      var parts = [];
      for (var i = 0; i < node.rules.length; i++) {
        parts.push(generate(node.rules[i]));
      }
      return parts.join('\n');
    },

    rule: function(node) {
      var context = {
        env: {},
        action: null
      };
      return [
        'function peg$parse' + node.name + '(peg$state) {',
        '  return ' + makeStdCall('peg$rule',
          [JSON.stringify(node.name)], [node.expression], context) + ';',
        '}'].join('\n');
    },

    named: function(node, context) {
      return makeStdCall('peg$named', [JSON.stringify(node.name)], [node.expression], context);
    },

    choice: function(node, context) {
      if (node.alternatives.length == 1) {
        return generate(node.alternatives[0]);
      } else {
        return makeStdCall('peg$choice', [], node.alternatives, context);
      }
    },

    action: function(node, context) {
      var newContext = objects.clone(context);
      newContext.env = objects.clone(context.env);
      var jsExpr = makeClosure(generate(node.expression, newContext));
      return makeStdCall('peg$action',
        makeActionClosureArgs(node.code, newContext.env).concat([jsExpr]),
        [], context);
    },

    sequence: function(node, context) {
      return makeStdCall('peg$sequence', [], node.elements, context);
    },

    labeled: function(node, context) {
      context.env[node.label] = true;
      return makeStdCall('peg$labeled',  [JSON.stringify(node.label)], [node.expression], context);
    },

    text: function(node, context) {
      return makeStdCall('peg$text', [], node.expression, context);
    },

    simple_and: function(node, context) {
      return makeStdCall('peg$predicate', ['false'], [node.expression], context);
    },

    simple_not: function(node, context) {
      return makeStdCall('peg$not', ['true'], [node.expression], context);
    },

    optional: function(node, context) {
      return makeStdCall('peg$optional', [], [node.expression], context);
    },

    zero_or_more: function(node, context) {
      return makeStdCall('peg$star', [], [node.expression], context);
    },

    one_or_more: function(node, context) {
      return makeStdCall('peg$plus', [], [node.expression], context);
    },

    semantic_and: function(node, context) {
      return makeStdCall('peg$jsPredicate',
        makeActionClosureArgs(node.code, context.env).concat(['false']),
        [], context);
    },

    semantic_not: function(node, context) {
      return makeStdCall('peg$jsPredicate',
        makeActionClosureArgs(node.code, context.env).concat(['true']),
        [], context);
    },

    rule_ref: function(node, context) {
      return makeStdCall('peg$parse' + node.name, [], [], context);
    },

    literal: function(node, context) {
      return makeStdCall('peg$literal',
        [JSON.stringify(node.ignoreCase), JSON.stringify(node.value)],
        [], context);
    },

    "class": function(node, context) {
      if (node.parts.length > 0) {
        regexp = '/^['
          + (node.inverted ? '^' : '')
          + arrays.map(node.parts, function(part) {
              return part instanceof Array
                ? js.regexpClassEscape(part[0])
                  + '-'
                  + js.regexpClassEscape(part[1])
                : js.regexpClassEscape(part);
            }).join('')
          + ']/' + (node.ignoreCase ? 'i' : '');
      } else {
        /*
         * IE considers regexps /[]/ and /[^]/ as syntactically invalid, so we
         * translate them into euqivalents it can handle.
         */
        regexp = node.inverted ? '/^[\\S\\s]/' : '/^(?!)/';
      }

      return makeStdCall('peg$class', [regexp, JSON.stringify(node.rawText)], [], context);
    },

    any: function(node, context) {
      return makeStdCall('peg$any', [], [], context);
    }

  });

  var code = readSource('../../runtime/wrapper');
  var parts = [];

  var startRules = {};
  arrays.each(options.allowedStartRules, function (r) {
    startRules[r] = 'peg$parse' + r;
  });
  parts.push([
    '  function peg$parse(input) {',
    '    var peg$allowedStartRules = ' + JSON.stringify(startRules) + ';',
    '    var peg$startRuleFunction = peg$parse' + options.allowedStartRules[0] + ';',
    '    if ("startRule" in options) {',
    '      if (!(options.startRule in peg$startRuleFunctions)) {',
    '        throw new Error("Can\'t start parsing from rule \\"" + options.startRule + "\\".");',
    '      }',
    '',
    '      peg$startRuleFunction = peg$startRuleFunctions[options.startRule];',
    '    }'
    ].join('\n'));

  parts.push(
    readSource('../../runtime/parser-internal'),
    '',
    readSource('../../runtime/closure-helpers'),
    '',
    generate(ast),
    subexpressions.join('\n'),
    '',
    '  var peg$state = new State();',
    '  var peg$success = peg$startRuleFunction(peg$state);',
    '',
    '    if (peg$success && peg$state.position === input.length) {',
    '      return peg$state.result;',
    '    } else {',
    '      if (peg$success && peg$state.position < input.length) {',
    '        peg$fail({ type: "end", description: "end of input" });',
    '      }',
    '',
    '      throw peg$buildException(',
    '        null,',
    '        peg$maxFailExpected,',
    '        peg$maxFailPos < input.length ? input.charAt(peg$maxFailPos) : null,',
    '        peg$maxFailPos < input.length',
    '          ? peg$computeLocation(peg$maxFailPos, peg$maxFailPos + 1)',
    '          : peg$computeLocation(peg$maxFailPos, peg$maxFailPos)',
    '      );',
    '    }',
    '  }',
    '  exports.parse = peg$parse;');

  code = code.replace('/*$PARSER*/', function() {return parts.join('\n');});
  ast.code = code;
}

module.exports = generateJavascript;
