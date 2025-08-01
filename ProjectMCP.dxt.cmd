@echo off
REM ------------------------------------------------------------
REM build_dxt.cmd – create a lean ProjectMCP .dxt package
REM ------------------------------------------------------------

REM ---- Settings ----------------------------------------------
set "EXT_NAME=ProjectMCP"      REM what you want the output file to be called
set "VERSION=0.1.0"            REM keep in sync with dxt.toml
set "SRC_DIR=pjpd"             REM path to the source folder (repo root)

REM ---- Derived values ----------------------------------------
set "OUT_FILE=%EXT_NAME%-%VERSION%.dxt"

echo Building %OUT_FILE% ...

del "%OUT_FILE%"

REM ---- Create the archive ------------------------------------
tar --format zip -a -c -f "%OUT_FILE%" ^
    -C "%SRC_DIR%" ^
    manifest.json ^
    .venv ^
    icon.png ^
    README.md ^
    LICENSE ^
    pyproject.toml ^
    projectmcp.toml ^
    resources ^
    src ^
    pjpd.py

echo Done! %OUT_FILE%
