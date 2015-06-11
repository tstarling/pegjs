  var peg$actionState = {
    savedPos: 0,
    currPos: 0,
  }
  var peg$FAILED = {};

  function State() {}

  State.prototype = {
    position: 0,
    env: {},
    silent: false,

    assign: function(source) {
      this.position = source.position;
      this.env = source.env;
      this.silent = source.silent;
    },

    clone: function() {
      var obj = new State;
      obj.position = this.position;
      obj.env = this.env;
      obj.silent = this.silent;
      return obj;
    }
  }

  function text() {
    return input.substring(peg$actionState.savedPos, peg$actionState.currPos);
  }

  function location() {
    return peg$computeLocation(peg$actionState.savedPos, peg$actionState.currPos);
  }

  function expected(description) {
    throw peg$buildException(
      null,
      [{ type: "other", description: description }],
      input.substring(peg$actionState.savedPos, peg$actionState.currPos),
      peg$computeLocation(peg$actionState.savedPos, peg$actionState.currPos)
    );
  }

  function error(message) {
    throw peg$buildException(
      message,
      null,
      input.substring(peg$actionState.savedPos, peg$actionState.currPos),
      peg$computeLocation(peg$actionState.savedPos, peg$actionState.currPos)
    );
  }

  function peg$failWithState(state, expected) {
    if (!state.silent) {
      peg$failAtPosition(state.position, expected);
    }
  }

  function peg$rule(state, name, exprFunc) {
    var newState = state.clone();
    newState.env = {};
    var result = exprFunc(newState);
    state.position = newState.position;
    return result;
  }

  function peg$traceDecorator(parseFunc) {
    return function(state, name, exprFunc) {
      var startPos = state.position;
      peg$tracer.trace({
        type:     "rule.enter",
        rule:     name,
        location: peg$computeLocation(startPos, startPos)
      });
      var result = parseFunc(state, name, exprFunc);
      if (result !== peg$FAILED) {
        peg$tracer.trace({
          type:     "rule.match",
          rule:     name,
          result:   result,
          location: peg$computeLocation(startPos, state.position)
        });
      } else {
        peg$tracer.trace({
          type: "rule.fail",
          rule: name,
          location: peg$computeLocation(startPos, startPos)
        });
      }
      return result;
    }
  }

  function peg$cacheDecorator(parseFunc) {
    return function(state, name, exprFunc) {
      var key    = state.position + ':' + name;
          cached = peg$resultsCache[key];

      if (cached) {
        state.position = cached.nextPos;
        return cached.result;
      }
      var result = parseFunc(state, name, exprFunc);
      peg$resultsCache[key] = {nextPos: state.position, result: result};
      return result;
    }
  }

  function peg$action(state, action, keys, exprFunc) {
    peg$actionState.savedPos = state.position;
    var result = exprFunc(state);
    if (result !== peg$FAILED) {
      peg$actionState.currPos = state.position;
      var args = [];
      for (var i = 0; i < keys.length; i++) {
        args.push(state.env[keys[i]]);
      }
      result = action.apply(this, args);
    }
    return result;
  }

  function peg$jsPredicate(state, predicate, keys, negate) {
    peg$actionState.savedPos = peg$actionState.currPos = state.position;
    var args = [];
    for (var i = 0; i < keys.length; i++) {
      args.push(state.env[keys[i]]);
    }
    var success = predicate.apply(this, args);
    if (negate) {
      success = !success;
    }
    return success ? (void 0) : peg$FAILED;
  }

  function peg$sequence(state, parts) {
    var newState = state.clone();
    var result = [], partResult;
    for (var i = 0; i < parts.length; i++) {
      partResult = parts[i](newState);
      if (partResult === peg$FAILED) {
        return peg$FAILED;
      } else {
        result.push(partResult);
      }
    }
    state.assign(newState);
    return result;
  }

  function peg$labeled(state, name, exprFunc) {
    var result = exprFunc(state);
    if (result !== peg$FAILED) {
      state.env[name] = result;
    } else {
      state.env[name] = null;
    }
    return result;
  }

  function peg$text(state, exprFunc) {
    var startPos = state.position;
    var result = exprFunc(state);
    if (result === peg$FAILED) {
      return peg$FAILED;
    } else {
      return input.substring(startPos, state.position);
    }
  }

  function peg$star(state, exprFunc) {
    var result = [], partResult;
    while (true) {
      partResult = exprFunc(state);
      if (partResult === peg$FAILED) {
        return result;
      }
      result.push(partResult);
    }
  }

  function peg$optional(state, exprFunc) {
    var result = exprFunc(state);
    return result === peg$FAILED ? null : result;
  }

  function peg$plus(state, exprFunc) {
    var partResult = exprFunc(state);
    if (partResult === peg$FAILED) {
      return peg$FAILED;
    }
    var result = [partResult];
    while (true) {
      partResult = exprFunc(state);
      if (partResult === peg$FAILED) {
        return result;
      }
      result.push(partResult);
    }
  }

  function peg$choice(state, parts) {
    for (var i = 0; i < parts.length; i++) {
      var partResult = parts[i](state);
      if (partResult !== peg$FAILED) {
        return partResult;
      }
    }
    return peg$FAILED;
  }

  function peg$predicate(state, negate, exprFunc) {
    var newState = state.clone();
    newState.silent = true;
    var success = exprFunc(newState) !== peg$FAILED;
    if (negate) {
      success = !success;
    }
    if (success) {
      return void 0;
    } else {
      return peg$FAILED;
    }
  }

  function peg$named(state, name, exprFunc) {
    var newState = state.clone();
    newState.silent = true;
    var result = exprFunc(newState);
    if (result !== peg$FAILED) {
      newState.silent = state.silent;
      state.assign(newState);
    } else {
      peg$failWithState(state, {
        type: 'other',
        description: name});
    }
    return result;
  }

  function peg$literal(state, ignoreCase, value) {
    var success;
    var s = input.substr(state.position, value.length);
    if (ignoreCase) {
      success = (s.toLowerCase() == value);
    } else {
      success = (s == value);
    }
    if (success) {
      state.position += s.length;
      return s;
    } else {
      peg$failWithState(state, {
        type: 'literal',
        value: value,
        description: JSON.stringify(value)});
      return peg$FAILED;
    }
  }

  function peg$class(state, regexp, rawText) {
    var c = input.charAt(state.position);
    if (regexp.test(c)) {
      state.position++;
      return c;
    } else {
      peg$failWithState(state, {
        type: "class",
        value: rawText,
        description: rawText});
      return peg$FAILED;
    }
  }

  function peg$any(state) {
    if (state.position < input.length) {
      return input.charAt(state.position++);
    } else {
      peg$failWithState(state, {
        type: "any",
        description: "any character"});
      return peg$FAILED;
    }
  }

  function peg$removeExpectedDuplicates(expected) {
    var i = 0;
    var blobs = {};
    while (i < expected.length) {
      var blob = JSON.stringify(expected[i]);
      if (blob in blobs) {
        expected.splice(i, 1);
      } else {
        blobs[blob] = true;
        i++;
      }
    }
  }
