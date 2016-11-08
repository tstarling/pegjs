/*
 * PEG.js 0.8.0
 *
 * http://pegjs.org/
 *
 * Copyright (c) 2010-2013 David Majda
 * Licensed under the MIT license.
 */
var PEG = (function(undefined) {
  "use strict";

  var endsWith = function(subjectString, searchString, position) {
    if (typeof position !== 'number' || !isFinite(position) || Math.floor(position) !== position || position > subjectString.length) {
      position = subjectString.length;
    }
    position -= searchString.length;
    var lastIndex = subjectString.indexOf(searchString, position);
    return lastIndex !== -1 && lastIndex === position;
  };

  var files = {
    _content: {},
    define: function(name, content) {
      this._content[name] = content;
    },
    get: function(name) {
      for (var key in this._content) {
        if (endsWith(name, key))
          return this._content[key];
      }
      return null;
    }
  };

  var modules = {
    define: function(name, factory) {
      var dir    = name.replace(/(^|\/)[^/]+$/, "$1"),
          module = { exports: {} };

      function require(path) {
        if (path in modules)
          return modules[name];
        var name   = dir + path,
            regexp = /[^\/]+\/\.\.\/|\.\//;

        /* Can't use /.../g because we can move backwards in the string. */
        while (regexp.test(name)) {
          name = name.replace(regexp, "");
        }

        if (!modules[name]) {
          throw new Error("Module not found: " + name);
        }

        return modules[name];
      }

      function readSource(path) {
        return require(path).code;
      }

      factory(module, require, readSource);
      this[name] = module.exports;
    },
    fs: {
      readFileSync: function(name, encoding) {
          return files.get(name);
      }
    }
  };

/*$MODULES*/

  return modules.peg;
})();
