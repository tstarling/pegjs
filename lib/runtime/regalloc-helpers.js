// regalloc-helpers.js
function peg$traceDecorator(parseFunc, name) {
  return function(silent) {
    var startPos = peg$currPos;
    peg$tracer.trace({
      type:     "rule.enter",
      rule:     name,
      location: peg$computeLocation(startPos, startPos)
    });
    var result = parseFunc(silent);
    if (result !== peg$FAILED) {
      peg$tracer.trace({
        type:     "rule.match",
        rule:     name,
        result:   result,
        location: peg$computeLocation(startPos, peg$currPos)
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
  return function(silent) {
    var key    = peg$currPos + ':' + (silent ? 's' : '') + ':' + name;
    var cached = peg$resultsCache[key];

    if (cached) {
      peg$currPos = cached[1];
      return cached[0];
    }
    var result = parseFunc(silent);
    peg$resultsCache[key] = [result, peg$currPos];
    return result;
  }
}

