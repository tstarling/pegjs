  function peg$traceDecorator(parseFunc, name) {
    return function(pos, silent) {
      var startPos = pos;
      peg$tracer.trace({
        type:     "rule.enter",
        rule:     name,
        location: peg$computeLocation(startPos, startPos)
      });
      var result = parseFunc(pos, silent);
      if (result !== peg$FAILED) {
        peg$tracer.trace({
          type:     "rule.match",
          rule:     name,
          result:   result,
          location: peg$computeLocation(startPos, peg$tailPos)
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

  function peg$cacheDecorator(parseFunc, name) {
    return function(pos, silent) {
      var key    = pos + ':' + (silent ? 's' : '') + ':' + name;
      cached = peg$resultsCache[key];

      if (cached) {
        peg$tailPos = cached[1];
        return cached[0];
      }
      var result = parseFunc(pos, silent);
      peg$resultsCache[key] = [result, peg$tailPos];
      return result;
    }
  }

