  function State() {}

  State.prototype = {
    position: 0,
    result: [],
    env: {},
    silent: false,

    assign: function(source) {
      this.position = source.position;
      this.result = source.result;
      this.env = source.env;
      this.silent = source.silent;
    },

    clone: function() {
      var obj = new State;
      obj.position = this.position;
      obj.result = this.result;
      obj.env = this.env;
      obj.silent = this.silent;
      return obj;
    }
  }

  function peg$rule(state, name, exprFunc) {
    // TODO: cache
    return exprFunc(state);
  }

  function peg$action(state, action, keys, exprFunc) {
    if (exprFunc(state)) {
      var args = [];
      for (var i = 0; i < keys.length; i++) {
        args.push(state.env[keys[i]]);
      }
      action.apply(this, args);
    }
  }

  function peg$jsPredicate(state, predicate, keys, negate) {
    var args = [];
    for (var i = 0; i < keys.length; i++) {
      args.push(state.env[keys[i]]);
    }
    var success = predicate.apply(this, args);
    if (negate) {
      success = !success;
    }
    return success;
  }

  function peg$sequence(state, parts) {
    var newState = state.clone();
    for (var i = 0; i < parts.length; i++) {
      if (!parts[i](newState)) {
        return false;
      }
    }
    state.assign(newState);
    return true;
  }

  function peg$labeled(state, name, exprFunc) {
    var newState = state.clone();
    newState.result = [];
    var success = exprFunc(newState);
    if (success) {
      newState.result = state.result.concat(newState.result);
      newState.env[name] = newState.result;
      state.assign(newState);
    } else {
      state.env[name] = null;
    }
    return success;
  }

  function peg$text(state, exprFunc) {
    var newState = state.clone();
    newState.result = [];
    var success = exprFunc(newState);
    newState.result = state.result;
    newState.result.push(input.substring(state.position, newState.position));
    state.assign(newState);
    return success;
  }

  function peg$star(state, exprFunc) {
    while (exprFunc(state));
    return true;
  }

  function peg$optional(state, exprFunc) {
    var newState = state.clone();
    if (exprFunc(newState)) {
      state.assign(newState);
    }
    return true;
  }

  function peg$plus(state, exprFunc) {
    if (!exprFunc(state)) {
      return false;
    }
    while (exprFunc(state));
    return true;
  }

  function peg$choice(state, parts) {
    for (var i = 0; i < parts.length; i++) {
      var newState = state.clone();
      if (parts[i](newState)) {
        state.assign(newState);
        return true;
      }
    }
    return false;
  }

  function peg$predicate(state, negate, exprFunc) {
    var newState = state.clone();
    newState.silent = true;
    newState.result = [];
    var success = exprFunc(newState);
    if (negate) {
      success = !success;
    }
    if (success) {
      state.result.push(undefined);
      return true;
    } else {
      return false;
    }
  }

  function peg$named(state, name, exprFunc) {
    var newState = state.clone();
    newState.silent = true;
    if (exprFunc(newState)) {
      newState.silent = state.silent;
      state.assign(newState);
      return true;
    } else {
      peg$fail({
        type: 'other',
        description: name
      });
      return false;
    }
  }

  function peg$literal(state, ignoreCase, value) {
    if (value.length == 0) {
      state.result.push('');
      return true;
    }
    var success;
    var s = input.substr(state.position, value.length);
    if (ignoreCase) {
      success = (s.toLowerCase() == value);
    } else {
      success = (s == value);
    }
    if (success) {
      state.result.push(s);
      state.position += s.length;
      return true;
    } else {
      peg$fail({
        type: 'literal',
        value: value,
        description: JSON.stringify(value)
      });
      return false;
    }
  }

  function peg$class(state, regexp, rawText) {
    var c = input.charAt(state.position);
    if (regexp.test(c)) {
      state.result.push(c);
      state.position++;
      return true;
    } else {
      peg$fail({
        type: "class",
        value: rawText,
        description: rawText});
      return false;
    }
  }

  function peg$any(state) {
    if (state.position < input.length) {
      state.result.push(input.charAt(state.position));
      state.position++;
      return true;
    } else {
      peg$fail({ type: "any", description: "any character" });
      return false;
    }
  }

