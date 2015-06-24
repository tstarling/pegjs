"use strict";

(function(root, factory) {
  if (typeof module !== 'undefined' && module.exports) {
    module.exports = factory;
  } else {
    root.Runner = factory(root.PEG);
  }
}(this, function(PEG) {

  return {
    run: function(benchmarks, runCount, options, callbacks) {

      /* Queue */

      var Q = {
        functions: [],

        add: function(f) {
          this.functions.push(f);
        },

        run: function() {
          for (var i = 0; i < this.functions.length; i++) {
            this.functions[i]();
          }
        }
      };

      /*
       * The benchmark itself is factored out into several functions (some of them
       * generated), which are enqueued and run one by one using |setTimeout|. We
       * do this for two reasons:
       *
       *   1. To avoid bowser mechanism for interrupting long-running scripts to
       *      kick-in (or at least to not kick-in that often).
       *
       *   2. To ensure progressive rendering of results in the browser (some
       *      browsers do not render at all when running JavaScript code).
       *
       * The enqueued functions share state, which is all stored in the properties
       * of the |state| object.
       */

      var state = {}, i, j;

      function initialize() {
        callbacks.start();

        state.totalInputSize = 0;
        state.totalParseTime = 0;
      }

      function benchmarkInitializer(i) {
        return function() {
          callbacks.benchmarkStart(benchmarks[i]);

          state.parser = PEG.buildParser(
            callbacks.readFile("../examples/" + benchmarks[i].id + ".pegjs"),
            options
          );
          state.benchmarkInputSize = 0;
          state.benchmarkParseTime = 0;
        };
      }

      function testRunner(i, j) {
        return function() {
          var benchmark = benchmarks[i],
              test      = benchmark.tests[j],
              input, parseTime, averageParseTime, k, t;

          callbacks.testStart(benchmark, test);

          input = callbacks.readFile(benchmark.id + "/" + test.file);

          t = process.hrtime();
          for (k = 0; k < runCount; k++) {
            state.parser.parse(input);
          }
          t = process.hrtime(t);
          parseTime = t[0]*1e3 + t[1]/1e6;
          averageParseTime = parseTime / runCount;

          callbacks.testFinish(benchmark, test, input.length, averageParseTime);

          state.benchmarkInputSize += input.length;
          state.benchmarkParseTime += averageParseTime;
        };
      }

      function benchmarkFinalizer(i) {
        return function() {
          callbacks.benchmarkFinish(
            benchmarks[i],
            state.benchmarkInputSize,
            state.benchmarkParseTime
          );

          state.totalInputSize += state.benchmarkInputSize;
          state.totalParseTime += state.benchmarkParseTime;
        };
      }

      function finalize() {
        callbacks.finish(state.totalInputSize, state.totalParseTime);
      }

      /* Main */

      Q.add(initialize);
      for (i = 0; i < benchmarks.length; i++) {
        Q.add(benchmarkInitializer(i));
        for (j = 0; j < benchmarks[i].tests.length; j++) {
          Q.add(testRunner(i, j));
        }
        Q.add(benchmarkFinalizer(i));
      }
      Q.add(finalize);

      Q.run();
    }
  };

}));
