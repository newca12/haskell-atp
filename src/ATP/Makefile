
default : atp

FILES = $(shell ls *.lhs Makefile)

GHC = ghc

PROFILE = # -prof -auto-all

# atp +RTS -p

.PHONY : check_profile
check_profile : 
ifneq ($(strip $(PROFILE)),)
	@echo ""
	@echo "!!! Warning: Profiling is ON !!!: " $(PROFILE)
	@echo ""
endif

GHC_OPTIONS = \
-XDeriveDataTypeable \
-XTemplateHaskell \
-XQuasiQuotes
# -XMultiParamTypeClasses 
# -XFlexibleInstances 
# -XNoMonomorphismRestriction 
# -XPatternSignatures 
# -fallow-undecidable-instances

#  allows use of GHC options in files during ghci calls
GHC_WARNINGS = \
-fwarn-deprecations \
-fwarn-dodgy-imports \
-fwarn-hi-shadowing \
-fwarn-implicit-prelude \
-fwarn-incomplete-patterns \
-fwarn-missing-fields \
-fwarn-missing-methods \
-fwarn-missing-signatures \
-fwarn-orphans \
-fwarn-overlapping-patterns \
-fwarn-monomorphism-restriction \
-fwarn-tabs \
-fwarn-type-defaults \
-fwarn-unused-binds \
-fwarn-unused-imports \
-fwarn-unused-matches \
-fno-warn-incomplete-record-updates \
-fno-warn-simple-patterns \

atp : $(FILES) check_profile
	$(GHC) $(GHC_OPTIONS) $(GHC_WARNINGS) $(PROFILE) -o $@ --make Main.lhs 

clean : 
	-rm -f atp Main *.hi *.o ExprParser.hs FormulaParser.hs ExprLexer.hs 
