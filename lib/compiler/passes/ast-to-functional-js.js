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
  var labelIndex = 0;

  function indent2(code)  { return code.replace(/^(.+)$/gm, '  $1');       }

  function buildCall(name, args) {
    return [
      name,
      '(',
      args.join(','),
      ')'].join('');
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

  function makeStdCall(name, expressions, nodes, env) {
    var args = ['peg$state'].concat(expressions);
    var arg, argArray, i, j;
    for (i = 0; i < nodes.length; i++) {
      if (nodes[i] instanceof Array) {
        argArray = [];
        for (j = 0; j < nodes[i].length; j++) {
          argArray.push(makeClosure(generate(nodes[i][j], env)));
        }
        arg = '[' + argArray.join(',') + ']';
      } else {
        arg = makeClosure(generate(nodes[i], env));
      }
      args.push(arg);
    }
    return buildCall(name, args);
  }

  function makeActionClosureArgs(code, env) {
    return [
      'function (' + objects.keys(env).join(', ') + ') {\n' +
        '    ' + code + '\n' +
      '  }',
      JSON.stringify(objects.values(env))];
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
      var env = {};
      labelIndex = 1;
      return [
        'function peg$parse' + node.name + '(peg$state) {',
        '  return ' + makeStdCall('peg$rule',
          [JSON.stringify(node.name)], [node.expression], env) + ';',
        '}'].join('\n');
    },

    named: function(node, env) {
      return makeStdCall('peg$named', [JSON.stringify(node.name)], [node.expression], env);
    },

    choice: function(node, env) {
      if (node.alternatives.length == 1) {
        return generate(node.alternatives[0]);
      } else {
        return makeStdCall('peg$choice', [], [node.alternatives], objects.clone(env));
      }
    },

    action: function(node, env) {
      var newEnv = objects.clone(env);
      var jsExpr = makeClosure(generate(node.expression, newEnv));
      return makeStdCall('peg$action',
        makeActionClosureArgs(node.code, newEnv).concat([jsExpr]),
        [], env);
    },

    sequence: function(node, env) {
      if (node.elements.length == 1) {
        return generate(node.elements[0], env);
      } else {
        return makeStdCall('peg$sequence', [], [node.elements], env);
      }
    },

    labeled: function(node, env) {
      env[node.label] = ++labelIndex;
      return makeStdCall('peg$labeled',
          [labelIndex], [node.expression], objects.clone(env));
    },

    text: function(node, env) {
      return makeStdCall('peg$text', [], [node.expression], objects.clone(env));
    },

    simple_and: function(node, env) {
      return makeStdCall('peg$predicate', ['false'], [node.expression], objects.clone(env));
    },

    simple_not: function(node, env) {
      return makeStdCall('peg$predicate', ['true'], [node.expression], objects.clone(env));
    },

    optional: function(node, env) {
      return makeStdCall('peg$optional', [], [node.expression], objects.clone(env));
    },

    zero_or_more: function(node, env) {
      return makeStdCall('peg$star', [], [node.expression], objects.clone(env));
    },

    one_or_more: function(node, env) {
      return makeStdCall('peg$plus', [], [node.expression], objects.clone(env));
    },

    semantic_and: function(node, env) {
      return makeStdCall('peg$jsPredicate',
        makeActionClosureArgs(node.code, env).concat(['false']),
        [], env);
    },

    semantic_not: function(node, env) {
      return makeStdCall('peg$jsPredicate',
        makeActionClosureArgs(node.code, env).concat(['true']),
        [], env);
    },

    rule_ref: function(node, env) {
      return makeStdCall('peg$parse' + node.name, [], [], env);
    },

    literal: function(node, env) {
      if (node.value.length == 0) {
        return "''";
      } else {
        return makeStdCall('peg$literal',
          [JSON.stringify(node.ignoreCase), JSON.stringify(node.value)],
          [], env);
      }
    },

    "class": function(node, env) {
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

      return makeStdCall('peg$class', [regexp, JSON.stringify(node.rawText)], [], env);
    },

    any: function(node, env) {
      return makeStdCall('peg$any', [], [], env);
    }

  });

  var code = readSource('../../runtime/wrapper');
  var parts = [];

  var startRules = [];
  arrays.each(options.allowedStartRules, function (r) {
    startRules.push(r + ': peg$parse' + r);
  });
  parts.push([
    '  function peg$parse(input) {',
    '    var options = arguments.length > 1 ? arguments[1] : {},',
    '        parser = this,',
    '        peg$startRuleFunctions = {' + startRules.join(',') + '},',
    '        peg$startRuleFunction = peg$parse' + options.allowedStartRules[0] + ';',
    '    if ("startRule" in options) {',
    '      if (!(options.startRule in peg$startRuleFunctions)) {',
    '        throw new Error("Can\'t start parsing from rule \\"" + options.startRule + "\\".");',
    '      }',
    '',
    '      peg$startRuleFunction = peg$startRuleFunctions[options.startRule];',
    '    }'
    ].join('\n'));

  parts.push(
    readSource('../../runtime/common-helpers'),
    '',
    readSource('../../runtime/closure-helpers'),
    '');

  if (options.cache) {
    parts.push(
      '  var peg$resultsCache = {};',
      '  peg$rule = peg$cacheDecorator(peg$rule);');
  }
  if (options.trace) {
    parts.push(
      '  peg$rule = peg$traceDecorator(peg$rule);',
      '  var peg$tracer = "tracer" in options ? options.tracer : new peg$DefaultTracer();',
      '');
  }

  var generated = generate(ast);
  if (ast.initializer) {
    parts.push(indent2("{" + ast.initializer.code + "}"));
    parts.push('');
  }

  parts.push(
    generated,
    subexpressions.join('\n'),
    '',
    '  var peg$state = new State();',
    '  var peg$result = peg$startRuleFunction(peg$state);',
    '',
    '    if (peg$result !== peg$FAILED && peg$state.position === input.length) {',
    '      return peg$result;',
    '    } else {',
    '      if (peg$result !== peg$FAILED && peg$state.position < input.length) {',
    '        peg$failWithState(peg$state, { type: "end", description: "end of input" });',
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
  code = code.replace('/*$TRACER*/', function() {
    return options.trace ? readSource('../../runtime/tracer') : '';
  });
  ast.code = code;
}

module.exports = generateJavascript;
