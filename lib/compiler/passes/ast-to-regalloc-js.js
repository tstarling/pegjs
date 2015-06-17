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

  function indent2(code)  { return code.replace(/^(.+)$/gm, '  $1');       }
  function indent4(code)  { return code.replace(/^(.+)$/gm, '    $1');       }

  function indent(code, level) {
    var i, spaces;
    for (i = 0; i < level; i++) {
      spaces += ' ';
    }
    if (Array.isArray(code)) {
      code = code.join('\n');
    }
    return code.replace(/^(.+)$/gm, function(s) {
      return spaces + s;
    });
  }

  function indentBlock(block, level) {
    block = arrays.map(block, function(line) {
      return indent(line, level);
    });
    return block;
  }

  function Context() {
    this.env = {};
    this.resultReg_ = false;
    this.silence_ = 'silence';
  }
  Context.prototype = {
    clone: function() {
      return Object.create(this);
    },

    /**
     * Get the result register specified owned by the caller, or create a new
     * register owned by the callee if there was none. Set the expression of
     * the specified result to this register.
     */
    getResultReg: function(result) {
      if (this.resultReg_ === false) {
        this.resultReg_ = allocReg(result.free);
      }
      result.expression = this.resultReg_;
      return this.resultReg_;
    },

    /**
     * This function fixes a result which has an incorrect expression. If the
     * context specifies a result register, the expression must be set to it.
     */
    fixResult: function(result) {
      if (this.resultReg_ !== false && this.resultReg_ != result.expression) {
        var assignment = this.resultReg_ + ' = ' + result.expression + ';';
        if (result.successBlock.length || result.failBlock.length) {
          // If there is a successBlock, it is possible that the preconditons
          // for the expression are established there, so we can't access the
          // expression in result.block. But we can't put it in result.epilogue
          // either, since that would break onSuccess()/onFail() aggregation in
          // the caller, which often assumes that the success block has
          // access to the result register. So we add the assignment to both
          // branches.
          result.successBlock.push(assignment);
          result.failBlock.push(assignment);
        } else {
          result.block.push(assignment);
        }
        result.expression = this.resultReg_;
        freeReg(result.free, result);
        result.free = [];
      }
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

  /**
   * A result object has the following structure:
   *   - block: An array of lines of code which are executed initially
   *   - expression: JavaScript expression which gives the result
   *   - condition: The condition of an if/else statement following the block.
   *     If this is null, the default condition is used, which tests the
   *     expression for success.
   *   - successBlock: An array of lines executed if the condition succeeds.
   *   - failBlock: An array of lines executed if the condition fails.
   *   - epilogue: An array of lines executed after the end of the if/else
   *   - free: An array of registers which the expression may depend on, to be
   *     freed after all code referring to the expression has been output.
   * 
   * So in summary:
   *
   * block
   * if (condition) {
   *   successBlock
   * } else {
   *   failBlock
   * }
   * epilogue
   * return expression;
   *
   * The condition and epilogue may be bundled into "block", generating code
   * like the pseudocode above, by calling resolveBlock().
   *
   * Execution of the expression may be reordered with other expressions, so
   * it cannot have side effects or depend on peg$currPos.
   */
  function Result() {
    this.block = [];
    this.condition = null;
    this.expression = '';
    this.successBlock = [];
    this.failBlock = [];
    this.epilogue = [];
    this.free = [];
  }
  Result.prototype = {
    resolveBlock: function() {
      if (this.condition === 'true') {
        this.block = this.block.concat(this.successBlock);
      } else if (this.condition === 'false') {
        this.block = this.block.concat(this.failBlock);
      } else if (this.successBlock.length) {
        if (this.condition !== null) {
          this.block.push(['if (', this.condition, ') {'].join(''));
        } else {
          this.block.push(['if (', this.expression, '!== peg$FAILED) {'].join(''));
        }
        this.block.push(indent2(this.successBlock.join('\n')));
        if (this.failBlock.length) {
          this.block.push(
            '} else {',
            indent2(this.failBlock.join('\n')));
        }
        this.block.push('}');
      } else if (this.failBlock.length) {
        if (this.condition !== null) {
          this.block.push(['if (!(', this.condition, ')) {'].join(''));
        } else {
          this.block.push(['if (', this.expression, ' === peg$FAILED) {'].join(''));
        }
        this.block.push(
          indent2(this.failBlock.join('\n')),
          '}');
      }
      this.block = this.block.concat(this.epilogue);
      this.successBlock = [];
      this.failBlock = [];
      this.condition = null;
      this.epilogue = [];
      return this.block;
    },

    onSuccess: function(b) {
      if (!Array.isArray(b)) {
        throw new Error("onSuccess() must be given an array");
      }
      this.successBlock = this.successBlock.concat(b);
      return this;
    },

    onFailure: function(b) {
      if (!Array.isArray(b)) {
        throw new Error("onFailure() must be given an array");
      }
      this.failBlock = this.failBlock.concat(b);
      return this;
    },

    /**
     * Join another block after this one, assuming that the other block
     * will use the expression of the existing block, if any. So the blocks
     * are concatenated, and the expression is replaced. The old conditional
     * part is resolved, and the conditional part of the other becomes the
     * conditional part of the new result.
     */
    append: function(other) {
      this.free = this.free.concat(other.free);
      this.expression = other.expression;
      this.block = this.resolveBlock().concat(other.block);
      this.condition = other.condition;
      this.successBlock = other.successBlock;
      this.failBlock = other.failBlock;
      this.epilogue = other.epilogue;
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
   * If the result object is supplied, a comment will be added to the source.
   */
  function freeReg(reg, result) {
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
    if (result && reg.length) {
      var comment = '// free ' + reg.join(',');
      result.epilogue.push('// free ' + reg.join(','));
    }
  }

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
    var result = generate(node, context);
    context.fixResult(result);
    return result;
  }

  function buildSimplePredicate(node, context) {
    var result = new Result();
    var negate = node.type === 'simple_not';
    var posReg = allocPosReg();
    var reg = context.getResultReg(result);
    result.block = [posReg + ' = peg$currPos;'];
    var newContext = context.silence().cloneEnv();
    result.append(recurse(node.expression, newContext));
    if (negate) {
      result.resolveBlock();
      result.condition = reg + ' === peg$FAILED';
      result.onFailure([reg + ' = peg$FAILED;']);
    }
    result.onSuccess([reg + ' = void 0;']);
    if (negate) {
      result.onFailure([['peg$currPos = ', posReg, ';'].join('')]);
    } else {
      result.onSuccess([['peg$currPos = ', posReg, ';'].join('')]);
    }
    freeReg(posReg, result);
    return result;
  }

  function buildSemanticPredicate(node, context) {
    var result = new Result();
    var negate = node.type == 'semantic_not';
    var reg = context.getResultReg(result);
    result.block = ['peg$savedPos = peg$currPos;'];
    var func = makeActionFunc(node.code, context);
    var call = makeActionCall(func, context);
    result.block = [
      'peg$savedPos = peg$currPos;',
      [reg, ' = ', call, ';'].join('')
    ];
    if (negate) {
      result.condition = '!' + reg;
    } else {
      result.condition = reg;
    }
    result.onSuccess([reg + ' = void 0;']);
    result.onFailure([reg + ' = peg$FAILED;']);
    return result;
  }
  var generate = visitor.build({
    grammar: function(node) {
      var parts = [];
      for (var i = 0; i < node.rules.length; i++) {
        parts.push(generate(node.rules[i]), '');
      }
      return parts.join('\n');
    },

    rule: function(node) {
      var context = new Context();
      allocatedRegList = [];
      freeRegList = [];
      freePosRegList = [];
      regIndex = 0;
      seqIndex = 0;
      choiceIndex = 0;
      var result = recurse(node.expression, context);
      var body = [
        allocatedRegList.length ? ['  var ', allocatedRegList.join(','), ';'].join('') : '',
        indent2(result.resolveBlock().join('\n')),
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
      var result = new Result();
      var reg = context.getResultReg(result);
      var silence = context.getSilence();
      result.block = [
        [reg, ' = ', 'peg$parse' + node.name, '(', silence, ');'].join('')];
      return result;
    },

    named: function(node, context) {
      var result = new Result();
      var reg = context.getResultReg(result);
      result.append(recurse(node.expression, context.silence()));
      if (context.getSilence() != 'true') {
        result.onFailure([makeFailCall({type: 'other', description: node.name}, context)]);
      }
      return result;
    },

    choice: function(node, context) {
      if (node.alternatives.length == 1) {
        return recurse(node.alternatives[0]);
      } else {
        var result = new Result();
        var label = 'choice_' + (++choiceIndex);
        result.block = [label + ': {'];
        var i;
        var reg = context.getResultReg(result);
        var newContext = context.cloneEnv().resultReg(reg);
        for (i = 0; i < node.alternatives.length; i++) {
          result.append(recurse(node.alternatives[i], newContext), 2);
          if (i != node.alternatives.length - 1) {
            result.onSuccess([['break ', label, ';'].join('')]);
          }
        }
        result.resolveBlock();
        result.block.push('} // ' + label);
        return result;
      }
    },

    action: function(node, context) {
      var result = new Result();
      var reg = context.getResultReg(result);
      var newContext = context.cloneEnv();
      var savedPos = allocPosReg();
      var subresult = recurse(node.expression, newContext);
      var func = makeActionFunc(node.code, newContext);
      result.block = [[savedPos, ' = peg$currPos;'].join('')];
      result.append(subresult);
      result.onSuccess([
        ['peg$savedPos = ', savedPos, ';'].join(''),
        [reg, ' = ', makeActionCall(func, newContext), ';'].join('')
      ]);
      return result;
    },

    sequence: function(node, context) {
      if (node.elements.length == 1) {
        return recurse(node.elements[0], context);
      } else {
        var posReg = allocPosReg();
        var result = new Result();
        var resultReg = context.getResultReg(result);
        var label = 'seq_' + (++seqIndex);
        result.block = [
          label + ': {',
          [posReg + ' = peg$currPos;'].join('')];
        var parts = [], i;
        for (i = 0; i < node.elements.length; i++) {
          var partReg = allocReg(result.free);
          var subresult = recurse(node.elements[i], context.resultReg(partReg));
          freeReg(subresult.free, subresult);
          subresult.free = [];
          result.append(subresult);
          parts.push(partReg);
          result.onFailure([
            ['peg$currPos = ', posReg, ';'].join(''),
            [resultReg, ' = peg$FAILED;'].join(''),
            ['break ', label, ';'].join('')
            ]);
          result.resolveBlock();
        }
        result.block.push(
          [resultReg, ' = [', parts.join(','), '];'].join(''),
          '} // ' + label );
        result.expression = resultReg;
        freeReg(result.free.concat([posReg]), result);
        result.free = [];
        return result;
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
      var result = new Result();
      var reg = context.getResultReg(result);
      result.block = [startPos + ' = peg$currPos;'];
      result.append(recurse(node.expression, context.cloneEnv()));
      result.onSuccess([
        [reg, ' = input.substring(', startPos, ',peg$currPos);'].join('')
      ]);
      freeReg([startPos], result);
      return result;
    },

    simple_and: buildSimplePredicate,
    simple_not: buildSimplePredicate,

    optional: function(node, context) {
      var result = new Result();
      var reg = context.getResultReg(result);
      result.append(recurse(node.expression, context.cloneEnv()));
      result.onFailure([reg + ' = null;']);
      // failure of the subexpression doesn't propagate back, so resolve the
      // block to prevent failure block concatenation.
      result.resolveBlock();
      // Always succeed
      result.condition = 'true';
      return result;
    },

    zero_or_more: function(node, context) {
      var result = new Result();
      var resultReg = context.getResultReg(result);
      var partReg = allocReg([]);
      var newContext = context.resultReg(partReg).cloneEnv();
      var subresult = recurse(node.expression, newContext);
      result.block = [resultReg + ' = [];'].concat(subresult.resolveBlock());

      // Generate the subresult again for the loop body
      subresult = recurse(node.expression, newContext);
      result.block.push(
        ['while (', partReg, ' !== peg$FAILED) {'].join(''),
        ['  ', resultReg, '.push(', partReg, ');'].join(''),
        indent2(subresult.resolveBlock().join('\n')),
        '}');
      freeReg(partReg, result);
      freeReg(subresult.free, result);
      // Always succeed
      result.condition = 'true';
      return result;
    },

    one_or_more: function(node, context) {
      var result = new Result();
      var resultReg = context.getResultReg(result);
      var initialFree = result.free;
      result.free = [];
      var partReg = allocReg([]);
      var newContext = context.resultReg(partReg).cloneEnv();
      var subresult = recurse(node.expression, newContext);
      result.append(subresult);
      result.onFailure([[resultReg, ' = peg$FAILED;'].join('')]);

      // Generate the subresult again for the loop body
      subresult = recurse(node.expression, newContext);
      result.onSuccess([
        resultReg + ' = [];',
        ['while (', partReg, ' !== peg$FAILED) {'].join(''),
        ['  ', resultReg, '.push(', partReg, ');'].join(''),
        indent2(subresult.resolveBlock().join('\n')),
        '}'
      ]);
      result.resolveBlock();
      freeReg(partReg, result);
      freeReg(result.free, result);
      result.free = initialFree;
      result.expression = resultReg;
      return result;
    },

    semantic_and: buildSemanticPredicate,
    semantic_not: buildSemanticPredicate,

    literal: function(node, context) {
      var result = new Result();
      // Special case: empty string always matches
      if (node.value.length == 0) {
        result.expression = "''";
        return result;
      }

      var reg = context.getResultReg(result);
      if (node.value.length == 1 && !node.ignoreCase) {
        result.condition = 'input.charCodeAt(peg$currPos) === ' + node.value.charCodeAt(0);
        result.onSuccess([[reg, ' = ', JSON.stringify(node.value), ';'].join('')]);
      } else {
        if (node.value.length == 1) {
          result.block.push([reg, ' = input.charAt(peg$currPos);'].join(''));
        } else {
          result.block.push([reg, ' = ',
            'input.substr(peg$currPos,', node.value.length, ');'].join(''));
        }
        if (node.ignoreCase) {
          result.condition = [reg, '.toLowerCase() === ',
            JSON.stringify(node.value)].join('');
        } else {
          result.condition = [reg, ' === ',
            JSON.stringify(node.value)].join('');
        }
      }
      result.onSuccess([['peg$currPos += ', node.value.length, ';'].join('')]);
      if (context.getSilence() != 'true') {
        result.onFailure([
          makeFailCall({
            type: 'literal',
            value: node.value,
            description: JSON.stringify(node.value)
          }, context)]);
      }
      result.onFailure([reg + ' = peg$FAILED;']);
      return result;
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
      var result = new Result();
      var reg = context.getResultReg(result);
      result.block = [reg + ' = input.charAt(peg$currPos);'];
      result.condition = [regexp, '.test(', reg, ')'].join('');
      result.onSuccess(['peg$currPos++;']);
      result.onFailure([reg + ' = peg$FAILED;']);
      if (context.getSilence() != 'true') {
        result.onFailure([makeFailCall({
          type: "class",
          value: node.rawText,
          description: node.rawText
        }, context)]);
      }
      return result;
    },

    any: function(node, context) {
      var result = new Result();
      var reg = context.getResultReg(result);
      result.condition = 'peg$currPos < input.length';
      result.onSuccess([reg + ' = input.charAt(peg$currPos++);']);
      result.onFailure([reg + ' = peg$FAILED;']);
      if (context.getSilence() != 'true') {
        result.onFailure([makeFailCall({
          type: "any",
          description: "any character"}, context)]);
      }
      return result;
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
    '  // start',
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
    '      peg$fail({ type: "end", description: "end of input" });',
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
