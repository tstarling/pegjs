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
  var consts = [];
  var constIndexes = {};

  var allocatedRegList = [];
  var freeRegList = [];
  var freePosRegList = [];
  var regIndex = 0;
  var seqIndex = 0;
  var choiceIndex = 0;

  function Context() {
    this.env = {};
    this.resultReg_ = false;
    this.silence_ = 'silence';
  }
  Context.prototype = {
    clone: function() {
      return Object.create(this);
    },

    hasResultReg: function() {
      return this.resultReg_ !== false;
    },

    getResultReg: function(free) {
      if (this.resultReg_ === false) {
        this.resultReg_ = allocReg(free);
      }
      return this.resultReg_;
    },

    getSilence: function() {
      return this.silence_;
    },

    silence: function() {
      var obj = this.clone();
      obj.silence_ = 'true';
      return obj;
    },

    resultReg: function(value) {
      var obj = this.clone();
      obj.resultReg_ = value;
      return obj;
    },

    cloneEnv: function() {
      var obj = this.clone();
      obj.env = objects.clone(obj.env);
      return obj;
    },

    noPassThru: function() {
      var obj = this.clone();
      obj.resultReg_ = false;
      return obj;
    }
  };

  function allocReg(free) {
    var reg;
    if (!Array.isArray(free)) {
      throw new Error("allocReg() must be given a free list");
    }
    if (freeRegList.length) {
      reg = freeRegList.pop();
    } else {
      reg = 'r' + (++regIndex);
      allocatedRegList.push(reg);
    }
    free.push(reg);
    return reg;
  }

  function allocPosReg() {
    var reg;
    if (freePosRegList.length) {
      reg = freePosRegList.pop();
    } else {
      reg = 'p' + (++regIndex);
      allocatedRegList.push(reg);
    }
    return reg;
  }

  /**
   * Free a register or array of registers. Note that this is a kind of
   * compile-time allocation. By calling this function, you are promising
   * that no more code will be generated that refers to the freed register.
   *
   * If the block is supplied, a comment will be added to the source.
   */
  function freeReg(reg, block) {
    if (!Array.isArray(reg)) {
      reg = [reg];
    }
    var i;
    for (i = 0; i < reg.length; i++) {
      if (/^p/.test(reg[i])) {
        freePosRegList.push(reg[i]);
      } else {
        freeRegList.push(reg[i]);
      }
    }
    if (block && reg.length) {
      var comment = '// free ' + reg.join(',');
      if (block.length) {
        block[block.length-1] += ' ' + comment;
      } else {
        block.push(comment);
      }
    }
  }

  function indent2(code)  { return code.replace(/^(.+)$/gm, '  $1');       }
  function indent4(code)  { return code.replace(/^(.+)$/gm, '    $1');       }

  function buildCall(name, args) {
    return [
      name,
      '(',
      args.join(','),
      ')'].join('');
  }

  function addConst(obj) {
    var str = JSON.stringify(obj);
    if (str in constIndexes) {
      return 'peg$' + constIndexes[str];
    } else {
      var index = consts.length;
      constIndexes[str] = index;
      consts.push(['var peg$', index, ' = ', str, ';'].join(''));
      return 'peg$' + index;
    }
  }

  function makeActionFunc(code, context) {
    var code = '(' + objects.keys(context.env).join(', ') + ') {\n'
        + code + '\n' + '}';
    if (code in constIndexes) {
      return 'peg$' + constIndexes[code];
    } else {
      var index = consts.length;
      constIndexes[code] = index;
      consts.push('function peg$' + index + code);
      return 'peg$' + index;
    }
  }

  function makeActionCall(func, context) {
    return [func, '(', objects.values(context.env).join(','), ')'].join('');
  }

  function makeFailCall(value, context) {
    var silence = context.getSilence();
    if (silence == 'true') {
      return '';
    }
    var constValue = addConst(value);
    var call = ['peg$fail(', constValue, ')'].join('');
    if (silence == 'false') {
      return call + ';';
    } else {
      return ['if (!', silence, ') ', call, ';'].join('');
    }
  }

  function recurse(node, context) {
    var res = generate(node, context);
    if (context.hasResultReg() && context.getResultReg() != res.expression) {
      res.block.push(context.getResultReg() + ' = ' + res.expression + ';');
      res.expression = context.getResultReg();
      freeReg(res.free, res.block);
      res.free = [];
    }
    return res;
  }

  function buildSimplePredicate(node, context) {
      var negate = node.type === 'simple_not';
      var posReg = allocPosReg();
      var newContext = context.silence().cloneEnv();
      var subresult = recurse(node.expression, newContext);
      var expression = [
        '((', subresult.expression, ' === peg$FAILED) ? ',
        negate ? 'void 0 : peg$FAILED' : 'peg$FAILED : void 0',
        ')'].join('');
      var block = [
        posReg + ' = peg$currPos;',
        subresult.block.join('\n'),
        ['peg$currPos = ', posReg, ';'].join('')];
      freeReg(posReg, block);

      return {
        block: block,
        expression: expression,
        free: subresult.free
      };
  }

  function buildSemanticPredicate(node, context) {
    var block = ['peg$savedPos = peg$currPos;'];
    var func = makeActionFunc(node.code, context);
    var call = makeActionCall(func, context);
    var expression;
    if (node.type == 'semantic_and') {
      expression = ['((', call, ') ? void 0 : peg$FAILED)'].join('');
    } else {
      expression = ['((', call, ') ? peg$FAILED : void 0)'].join('');
    }

    // A JS predicate could have side-effects which prevent it from being reordered
    // So call getResultReg() to force ordering.
    var free = [];
    var reg = context.getResultReg(free);

    return {
      block: block,
      expression: expression,
      free: free
    };
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
      var context = new Context;
      allocatedRegList = [];
      freeRegList = [];
      freePosRegList = [];
      regIndex = 0;
      seqIndex = 0;
      choiceIndex = 0;
      var result = recurse(node.expression, context);
      var body = [
        allocatedRegList.length ? ['  var ', allocatedRegList.join(','), ';'].join('') : '',
        indent2(result.block.join('\n')),
        ['  return ', result.expression, ';'].join(''),
        ''].join('\n');
      if (options.cache || options.trace) {
        var closure = ['function(silence) {\n', body, '}'].join('');
        if (options.cache) {
          closure = ['peg$cacheDecorator(', closure, ',', JSON.stringify(node.name), ')'].join('');
        }
        if (options.trace) {
          closure = ['peg$traceDecorator(', closure, ',', JSON.stringify(node.name), ')'].join('');
        }
        return ['var peg$parse', node.name, ' = ', closure, ';'].join('');
      } else {
        return ['function peg$parse', node.name, '(silence) {\n', body, '}'].join('');
      }
    },

    rule_ref: function(node, context) {
      var free = [];
      var reg = context.getResultReg(free);
      var silence = context.getSilence();
      var block = [
        [reg, ' = ', 'peg$parse' + node.name, '(', silence, ');'].join('')];
      return {
        block: block,
        expression: reg,
        free: free
      };
    },

    named: function(node, context) {
      var free = [];
      var reg = context.getResultReg(free);
      var subresult = recurse(node.expression, context.silence());
      var block = subresult.block;
      if (context.getSilence() != 'true') {
        block = block.concat([
          ['if (', reg, ' === peg$FAILED) {'].join(''),
          indent2(makeFailCall({type: 'other', description: node.name}, context)),
          '}']);
      }
      return {
        block: block,
        expression: reg,
        free: free
      };
    },

    choice: function(node, context) {
      if (node.alternatives.length == 1) {
        return recurse(node.alternatives[0]);
      } else {
        var label = 'choice_' + (++choiceIndex);
        var block = [label + ': {'];
        var free = [], i;
        var reg = context.getResultReg(free);
        var newContext = context.cloneEnv().resultReg(reg);
        for (i = 0; i < node.alternatives.length; i++) {
          var subresult = recurse(node.alternatives[i], newContext);
          block.push(indent2(subresult.block.join('\n')));
          if (i != node.alternatives.length - 1) {
            block.push(['  if (', reg, ' !== peg$FAILED) break ', label, ';'].join(''));
          }
          free = free.concat(subresult.free);
        }
        block.push('}');
        return {
          block: block,
          expression: reg,
          free: free.concat(subresult.free)
        };
      }
    },

    action: function(node, context) {
      var free = [];
      var reg = context.getResultReg(free);
      var newContext = context.cloneEnv();
      var savedPos = allocPosReg();
      var subresult = recurse(node.expression, newContext);
      free = free.concat(subresult.free);
      var func = makeActionFunc(node.code, newContext);
      var block = [[savedPos, ' = peg$currPos;'].join('')];
      block = block.concat(subresult.block);
      block.push(
        ['if (', reg, ' !== peg$FAILED) {'].join(''),
        ['  peg$savedPos = ', savedPos, ';'].join(''),
        ['  ', reg, ' = ', makeActionCall(func, newContext), ';'].join(''),
        '}');
      return {
        block: block,
        expression: reg,
        free: free
      };
    },

    sequence: function(node, context) {
      if (node.elements.length == 1) {
        return recurse(node.elements[0], context);
      } else {
        var posReg = allocPosReg();
        var free = [];
        var resultReg = context.getResultReg(free);
        var label = 'seq_' + (++seqIndex);
        var block = [
          posReg + ' = peg$currPos;',
          resultReg + ' = peg$FAILED;',
          label + ': {'];
        var parts = [], i;
        for (i = 0; i < node.elements.length; i++) {
          var reg = allocReg(free);
          var subresult = recurse(node.elements[i], context.resultReg(reg));
          block.push(indent2(subresult.block.join('\n')));
          freeReg(subresult.free, block);
          parts.push(reg);
          block.push(['  if (', reg, ' === peg$FAILED) break ', label, ';'].join(''));
        }
        block.push(
          ['  ', resultReg, ' = [', parts.join(','), '];'].join(''),
          '}',
          ['if (', resultReg, ' === peg$FAILED) {'].join(''),
          ['  peg$currPos = ', posReg, ';'].join(''),
          '}');
        freeReg(free.concat([posReg]), block);
        return {
          block: block,
          expression: resultReg,
          free: []
        };
      }
    },

    labeled: function(node, context) {
      var reg = allocReg([]);
      context.env[node.label] = reg;
      var subresult = recurse(node.expression, context.cloneEnv().resultReg(reg));
      subresult.block.push(['// ', node.label, ' <- ', reg].join(''));
      return subresult;
    },

    text: function(node, context) {
      var startPos = allocPosReg();
      var block = [startPos + ' = peg$currPos;'];
      var subresult = recurse(node.expression, context.cloneEnv());
      block = block.concat(subresult.block);
      var endPos = allocPosReg();
      block.push(endPos + ' = peg$currPos;');
      return {
        block: block,
        expression: ['((', subresult.expression, ' === peg$FAILED) ',
          '? peg$FAILED : input.substring(', startPos, ',', endPos, '))'].join(''),
        free: [startPos, endPos].concat(subresult.free)
      };
    },

    simple_and: buildSimplePredicate,
    simple_not: buildSimplePredicate,

    optional: function(node, context) {
      var free = [];
      var reg = context.getResultReg(free);
      var subresult = recurse(node.expression, context.cloneEnv());
      var block = subresult.block;
      block.push(['if (', reg, ' === peg$FAILED) ', reg, ' = null;'].join(''));
      return {
        block: block,
        expression: reg,
        free: free.concat(subresult.free)
      };
    },

    zero_or_more: function(node, context) {
      var free = [];
      var resultReg = context.getResultReg(free);
      var partReg = allocReg([]);
      var subresult = recurse(node.expression, context.resultReg(partReg).cloneEnv());
      var srblock = subresult.block.join('\n');
      var block = [
        resultReg + ' = [];',
        srblock,
        ['while (', partReg, ' !== peg$FAILED) {'].join(''),
        ['  ', resultReg, '.push(', partReg, ');'].join(''),
        indent2(srblock),
        '}'];
      freeReg(partReg, block);
      freeReg(subresult.free, block);
      return {
        block: block,
        expression: resultReg,
        free: free
      };
    },

    one_or_more: function(node, context) {
      var free = [];
      var resultReg = context.getResultReg(free);
      var partReg = allocReg([]);
      var subresult = recurse(node.expression, context.resultReg(partReg).cloneEnv());
      var srblock = subresult.block.join('\n');
      var block = [
        srblock,
        ['if (', partReg, ' === peg$FAILED) {'].join(''),
        ['  ', resultReg, ' = peg$FAILED;'].join(''),
        '} else {',
        ['  ', resultReg, ' = [];'].join(''),
        ['  while (', partReg, ' !== peg$FAILED) {'].join(''),
        indent4(srblock),
        '   }',
        '}'];
      freeReg(partReg, block);
      freeReg(subresult.free, block);
      return {
        block: block,
        expression: resultReg,
        free: free
      };
    },

    semantic_and: buildSemanticPredicate,
    semantic_not: buildSemanticPredicate,

    literal: function(node, context) {
      // Special case: empty string always matches
      if (node.value.length == 0) {
        return {
          block: [],
          expression: "''",
          free: []
        };
      }

      var free = [];
      var reg = context.getResultReg(free);
      var block = [];
      if (node.value.length == 1 && !node.ignoreCase) {
        block.push(
          ['if (input.charCodeAt(peg$currPos) === ', node.value.charCodeAt(0), ') {'].join(''),
          ['  ', reg, ' = ', JSON.stringify(node.value), ';'].join(''));
      } else {
        if (node.value.length == 1) {
          block.push([reg, ' = input.charAt(peg$currPos);'].join(''));
        } else {
          block.push([reg, ' = input.substr(peg$currPos,', node.value.length, ');'].join(''));
        }
        if (node.ignoreCase) {
          block.push(
            ['if (', reg, '.toLowerCase() === ', JSON.stringify(node.value), ') {'].join(''));
        } else {
          block.push(
            ['if (', reg, ' === ', JSON.stringify(node.value), ') {'].join(''));
        }
      }
      block.push(
        ['  peg$currPos += ', node.value.length, ';'].join(''),
        '} else {');
      if (context.getSilence() != 'true') {
        block.push(indent2(makeFailCall({
          type: 'literal',
          value: node.value,
          description: JSON.stringify(node.value)
        }, context)));
      }
      block.push(
        ['  ', reg, ' = peg$FAILED;'].join(''),
        '}');
      return {
        block: block,
        expression: reg,
        free: free
      };
    },

    "class": function(node, context) {
      var regexp;
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
      var free = [];
      var reg = context.getResultReg(free);
      var block = [
        [reg, ' = input.charAt(peg$currPos);'].join(''),
        ['if (', regexp, '.test(', reg, ')) {'].join(''),
        '  peg$currPos++;',
        '} else {'];
      if (context.getSilence() != 'true') {
        block.push(indent2(makeFailCall({
          type: "class",
          value: node.rawText,
          description: node.rawText
        }, context)));
      }
      block.push(
        ['  ', reg, ' = peg$FAILED;'].join(''),
        '}');
      return {
        block: block,
        expression: reg,
        free: free
      };
    },

    any: function(node, context) {
      var free = [];
      var reg = context.getResultReg(free);
      var block = [
        ['if (peg$currPos < input.length) {'].join(''),
        ['  ', reg, ' = input.charAt(peg$currPos++);'].join(''),
        '} else {'];
      if (context.getSilence() != 'true') {
        block.push(indent2(makeFailCall({
          type: "any",
          description: "any character"}, context)));
      }
      block.push(
        ['  ', reg, ' = peg$FAILED;'].join(''),
        '}');
      return {
        block: block,
        expression: reg,
        free: free
      };
    }
  });


  var code = readSource('../../runtime/wrapper');
  var parts = [];

  var startRules = [];
  arrays.each(options.allowedStartRules, function (r) {
    startRules.push(r + ': peg$parse' + r);
  });
  var generated = generate(ast);
  parts.push('function peg$parse(input) {',
    '  "use strict";',
    '  var options = arguments.length > 1 ? arguments[1] : {},',
    '      parser = this,',
    '      peg$currPos = 0,',
    '      peg$savedPos = 0,',
    '      peg$FAILED = {};',
    '',
    indent2(readSource('../../runtime/common-helpers')),
    '',
    indent2(readSource('../../runtime/stackvm-helpers')),
    '',
    indent2(readSource('../../runtime/regalloc-helpers')),
    '',
    '// consts',
    consts.join('\n'),
    '',
    '// generated',
    generated,
    '',
    '  // epilogue',
    '',
    '  var peg$startRuleFunctions = {' + startRules.join(',') + '},',
    '      peg$startRuleFunction = peg$parse' + options.allowedStartRules[0] + ';',
    '  if ("startRule" in options) {',
    '    if (!(options.startRule in peg$startRuleFunctions)) {',
    '      throw new Error("Can\'t start parsing from rule \\"" + options.startRule + "\\".");',
    '    }',
    '',
    '    peg$startRuleFunction = peg$startRuleFunctions[options.startRule];',
    '  }');

  if (options.cache) {
    parts.push('  var peg$resultsCache = {};');
  }
  if (options.trace) {
    parts.push(
      '  var peg$tracer = "tracer" in options ? options.tracer : new peg$DefaultTracer();');
  }
  if (ast.initializer) {
    parts.push(indent2(ast.initializer.code));
    parts.push('');
  }

  parts.push(
    '  peg$currPos = 0;',
    '  var peg$result = peg$startRuleFunction(false);',
    '',
    '  if (peg$result !== peg$FAILED && peg$currPos === input.length) {',
    '    return peg$result;',
    '  } else {',
    '    if (peg$result !== peg$FAILED && peg$currPos < input.length) {',
    '      peg$failAtPosition(peg$currPos, { type: "end", description: "end of input" });',
    '    }',
    '',
    '    throw peg$buildException(',
    '      null,',
    '      peg$maxFailExpected,',
    '      peg$maxFailPos < input.length ? input.charAt(peg$maxFailPos) : null,',
    '      peg$maxFailPos < input.length',
    '        ? peg$computeLocation(peg$maxFailPos, peg$maxFailPos + 1)',
    '        : peg$computeLocation(peg$maxFailPos, peg$maxFailPos)',
    '    );',
    '  }',
    '}',
    'exports.parse = peg$parse;');

  code = code.replace('/*$PARSER*/', function() {return indent2(parts.join('\n'));});
  code = code.replace('/*$TRACER*/', function() {
    return options.trace ? readSource('../../runtime/tracer') : '';
  });
  ast.code = code;
}

module.exports = generateJavascript;
