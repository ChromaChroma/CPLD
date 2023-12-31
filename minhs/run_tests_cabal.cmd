@echo off
setlocal enableextensions EnableDelayedExpansion
if "!executable_set!" NEQ "1" (
    set cabal_version=
    for /f "delims=." %%a in ('cabal --numeric-version 2^>nul') do set cabal_version=%%a
    if "!cabal_version!" LSS "3" (
        echo Your cabal version should be at least 3.
        set full_version=
        for /f "delims=" %%a in ('cabal --numeric-version 2^>nul') do set full_version=%%a
        if "!full_version!" NEQ "" (
            echo ^(It reports version !full_version!^)
        )
        echo Please install Haskell using GHCup:
        echo    https://www.haskell.org/ghcup/
        echo and install the recommended versions of GHC and cabal. Installation of
        echo stack is optional.
        echo
        echo If you meant to use stack, use run_tests_stack.cmd instead of this one.
        exit /B 1
    )
)

if "!runhaskell_set!" NEQ "1" (
    set runhaskell=runhaskell
    set runhaskell_set=1
)
if "!executable_set!" NEQ "1" (
    for /f "delims=" %%a in ('cabal list-bin minhs1 2^>nul') do (
        set executable=%%a
        set executable_set=1
    )
)
if "!executable_set!" NEQ "1" (
    set executable=cabal exec minhs-1 --
)

!runhaskell! -i.\tests\driver .\tests\driver\Check.hs %* !executable!
