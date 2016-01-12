# ===== Variables =====

PEGJS_VERSION = `cat $(VERSION_FILE)`

# ===== Directories =====

SRC_DIR              = src
LIB_DIR              = lib
BIN_DIR              = bin
BROWSER_DIR          = browser
SPEC_DIR             = spec
BENCHMARK_DIR        = benchmark
NODE_MODULES_DIR     = node_modules
NODE_MODULES_BIN_DIR = $(NODE_MODULES_DIR)/.bin

# ===== Files =====

MAIN_FILE = $(LIB_DIR)/peg.js

PARSER_SRC_FILE = $(SRC_DIR)/parser.pegjs
PARSER_OUT_FILE = $(LIB_DIR)/parser.js

BROWSER_FILE_DEV = $(BROWSER_DIR)/peg-$(PEGJS_VERSION).js
BROWSER_FILE_MIN = $(BROWSER_DIR)/peg-$(PEGJS_VERSION).min.js

VERSION_FILE = VERSION

# ===== Executables =====

JSHINT        = $(NODE_MODULES_BIN_DIR)/jshint
BROWSERIFY    = $(NODE_MODULES_BIN_DIR)/browserify
UGLIFYJS      = $(NODE_MODULES_BIN_DIR)/uglifyjs
JASMINE_NODE  = $(NODE_MODULES_BIN_DIR)/jasmine-node
PEGJS         = $(BIN_DIR)/pegjs
BENCHMARK_RUN = $(BENCHMARK_DIR)/run

# ===== Targets =====

# Default target
all: browser

# Generate the grammar parser
parser:
	$(PEGJS) $(PARSER_SRC_FILE) $(PARSER_OUT_FILE)

# Build the browser version of the library
browser:
	mkdir -p $(BROWSER_DIR)

	rm -f $(BROWSER_FILE_DEV)
	rm -f $(BROWSER_FILE_MIN)

	# The following code is inspired by CoffeeScript's Cakefile.

	echo '/*'                                                                          >> $(BROWSER_FILE_DEV)
	echo " * PEG.js $(PEGJS_VERSION)"                                                  >> $(BROWSER_FILE_DEV)
	echo ' *'                                                                          >> $(BROWSER_FILE_DEV)
	echo ' * http://pegjs.org/'                                                        >> $(BROWSER_FILE_DEV)
	echo ' *'                                                                          >> $(BROWSER_FILE_DEV)
	echo ' * Copyright (c) 2010-2015 David Majda'                                      >> $(BROWSER_FILE_DEV)
	echo ' * Licensed under the MIT license.'                                          >> $(BROWSER_FILE_DEV)
	echo ' */'                                                                         >> $(BROWSER_FILE_DEV)

	$(BROWSERIFY) --standalone PEG $(MAIN_FILE) >> $(BROWSER_FILE_DEV)

	$(UGLIFYJS)                 \
	  --mangle                  \
	  --compress warnings=false \
	  --comments /Copyright/    \
	  -o $(BROWSER_FILE_MIN)    \
	  $(BROWSER_FILE_DEV)

# Remove browser version of the library (created by "browser")
browserclean:
	rm -rf $(BROWSER_DIR)

# Run the spec suite
spec:
	$(JASMINE_NODE) --verbose $(SPEC_DIR)

# Run the benchmark suite
benchmark:
	$(BENCHMARK_RUN)

# Run JSHint on the source
hint:
	$(JSHINT)                                                                \
	  `find $(LIB_DIR) -name '*.js'`                                         \
	  `find $(SPEC_DIR) -name '*.js' -and -not -path '$(SPEC_DIR)/vendor/*'` \
	  $(BENCHMARK_DIR)/*.js                                                  \
	  $(BENCHMARK_RUN)                                                       \
	  $(PEGJS)

.PHONY:  all parser browser browserclean spec benchmark hint
.SILENT: all parser browser browserclean spec benchmark hint
