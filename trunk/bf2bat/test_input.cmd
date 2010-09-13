@echo off
:read_line
set /p var=
set var="%var:"=""%"
echo %var%
goto read_line
