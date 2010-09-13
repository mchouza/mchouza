@echo off
set stack_index=0
set next_label_num=0
set output_path=%2
echo @echo off >%output_path%
echo ::Compiled representation of BF source file %1 >>%output_path%
echo set cell_num=0 >>%output_path%
echo set printable_chars=^^^ ^^^!^^^"^^^#^^^$^^^%%%%^^^&'^^^(^^^)^^^*^^^+^^^,^^^-^^^.^^^/^^^0^^^1^^^2^^^3^^^4^^^5^^^6^^^7^^^8^^^9^^^:^^^;^^^<^^^=^^^>^^^?^^^@^^^A^^^B^^^C^^^D^^^E^^^F^^^G^^^H^^^I^^^J^^^K^^^L^^^M^^^N^^^O^^^P^^^Q^^^R^^^S^^^T^^^U^^^V^^^W^^^X^^^Y^^^Z^^^[^^^\^^^]^^^^^^^_^^^`^^^a^^^b^^^c^^^d^^^e^^^f^^^g^^^h^^^i^^^j^^^k^^^l^^^m^^^n^^^o^^^p^^^q^^^r^^^s^^^t^^^u^^^v^^^w^^^x^^^y^^^z^^^{^^^|^^^}^^^~>>%output_path%
for /f "tokens=*" %%l in (%1) do call :proc_token "%%l"
goto :eof

:proc_token
if [%1]==[""] goto :eof
set t=%1
set t="%t:"=%"
:char_loop
set c="%t:~1,1%"
set t="%t:~2,-1%"
call :proc_char %c%
if [%t%] neq [""] goto char_loop
goto :eof

:proc_char
if %c% neq "<" goto not_lt
echo set /a cell_num=cell_num-1 >>%output_path%
goto :eof
:not_lt
if %c% neq ">" goto not_gt
echo set /a cell_num=cell_num+1 >>%output_path%
goto :eof
:not_gt
if %c% neq "+" goto not_plus
echo set /a cell_%%cell_num%%=(cell_%%cell_num%%+1)%%%%(256) >>%output_path%
goto :eof
:not_plus
if %c% neq "-" goto not_minus
echo set /a cell_%%cell_num%%=(cell_%%cell_num%%+255)%%%%(256) >>%output_path%
goto :eof
:not_minus
if %c% neq "." goto not_dot
echo set /a char_index=cell_%%cell_num%%-32 >>%output_path%
echo if %%char_index%% equ -22 (echo. ^&^& goto end_print_%next_label_num%) >>%output_path%
echo if %%char_index%% lss 0 goto end_print_%next_label_num% >>%output_path%
echo if %%char_index%% gtr 94 goto end_print_%next_label_num% >>%output_path%
echo (set idx_expr=printable_chars:~%%char_index%%,1)>>%output_path%
echo call set char="%%%%%%idx_expr%%%%%%" >>%output_path%
echo (echo.^|set/p=^^^^^^%%char:~1,1%%) >>%output_path%
echo :end_print_%next_label_num% >>%output_path%
set /a next_label_num=next_label_num+1
goto :eof
:not_dot
if %c% neq "," goto not_comma
echo COMMA >>%output_path%
goto :eof
:not_comma
if %c% neq "[" goto not_lsq
echo set /a cell_val=cell_%%cell_num%% >>%output_path%
echo if %%cell_val%%==0 goto :after_rsq_%next_label_num% >>%output_path%
echo :after_lsq_%next_label_num% >>%output_path%
call set stack_%stack_index%=%next_label_num%
set /a next_label_num=next_label_num+1
set /a stack_index=stack_index+1
goto :eof
:not_lsq
if %c% neq "]" goto not_rsq
set /a stack_index=stack_index-1
call set label_num=%%stack_%stack_index%%%
echo set /a cell_val=cell_%%cell_num%% >>%output_path%
echo if %%cell_val%% neq 0 goto :after_lsq_%label_num% >>%output_path%
echo :after_rsq_%label_num% >>%output_path%
goto :eof
:not_rsq
::other symbols are ignored
goto :eof