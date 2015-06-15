    // stackvm-helpers.js
    function peg$fail(expected) {
      return peg$failAtPosition(peg$currPos, expected);
    }

    function peg$removeExpectedDuplicates(expected) {
      var i = 1;
      /*
       * This works because the bytecode generator guarantees that every
       * expectation object exists only once, so it's enough to use |===| instead
       * of deeper structural comparison.
       */
      while (i < expected.length) {
        if (expected[i - 1] === expected[i]) {
          expected.splice(i, 1);
        } else {
          i++;
        }
      }
    }
