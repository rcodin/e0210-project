tc_no=$1
if [ $# -lt 1 ]
then
	echo "[replay.sh] Not enough arguments. test case is required"
	exit
fi

rm -r PoP_Replay/build > /dev/null 2> /dev/null
rm -r PoP_Replay/sootBin > /dev/null 2> /dev/null
rm global_trace > /dev/null 2> /dev/null

mkdir PoP_Replay/build
mkdir PoP_Replay/sootBin

echo "[replay.sh] Compiling PoP_Replay/src/*"
javac -source 1.8 -target 1.8 -cp ./lib/soot-nightly-05082016.jar -d PoP_Replay/build PoP_Replay/src/pop_replay/*
if [ $? -ne 0 ]
then
    echo "[replay.sh] Error in compiling replay code"
    exit 3
fi

echo "[replay.sh] Instrumenting test case $tc_no"
java -cp ./lib/soot-nightly-05082016.jar:./PoP_Replay/build pop_replay.PoP_Replay project-4 $tc_no 

if [ $? -ne 0 ]
then
    echo "[replay.sh] Error in instrumenting code for replay"
    exit 4
fi

    
    
input_args=`cat ./Testcases/project-4/input/$tc_no`
trial_replay_exit_code=""
echo "[replay.sh] Performing trial replay on Project-3 $tc_no sample output"
cp ./Testcases/output/project-3/$tc_no global_trace
timeout 10 java -cp ./PoP_Replay/sootBin "$tc_no.Main" $input_args > $tc_no.replay_run.stdout 2> $tc_no.replay_run.stderr
if [ $? -ne 0 ]
then
    trial_replay_exit_code="exit code $?"
fi

rm pathLog > /dev/null 2> /dev/null
rm global_trace > /dev/null 2> /dev/null

if [ "$trial_replay_exit_code" != "" ]
then
    echo "[replay.sh] Trial replay failed"
    exit 2
fi

echo "[replay.sh] Starting actual replay runs"

replayCnt=0
replayDone=1
correctPath=1
while [ $replayCnt -lt 10 ] && [ "$replayDone" == "1" ]
do
    replayCnt=$(( $replayCnt+1 ))	
    echo -n "[replay.sh] Replay iteration $replayCnt out of 10 :: "
    rm pathLog > /dev/null 2> /dev/null
    rm global_trace > /dev/null 2> /dev/null
    cp ./Testcases/project-4/processed-output/$tc_no.global_trace global_trace
    timeout 10 java -cp ./PoP_Replay/sootBin "$tc_no.Main" $input_args > $tc_no.replay_run.stdout 2> $tc_no.replay_run.stderr
    replay_exit_code=""
    if [ $? -ne 0 ]
    then
        replay_exit_code="exit code $?"
    fi

    

    rm Testcases/project-4/processed-output/$tc_no.replay_run.pathLog > /dev/null 2> /dev/null
    rm Testcases/project-4/processed-output/$tc_no.replay_run.stdout > /dev/null 2> /dev/null
    rm Testcases/project-4/processed-output/$tc_no.replay_run.stderr > /dev/null 2> /dev/null

    mv pathLog Testcases/project-4/processed-output/$tc_no.replay_run.pathLog
    mv $tc_no.replay_run.stdout Testcases/project-4/processed-output/$tc_no.replay_run.stdout
    mv $tc_no.replay_run.stderr Testcases/project-4/processed-output/$tc_no.replay_run.stderr


    

    if [ "$replay_exit_code" == "" ]
    then
        
        pathLog_2=`sort ./Testcases/project-4/processed-output/$tc_no.replay_run.pathLog`
        pathLog=`sort ./Testcases/project-4/output/$tc_no.record_run.pathLog`
        if [ "$pathLog" == "$pathLog_2" ]
        then
        echo "Replay: Complete. Correct Path: Pass"
        else
            correctPath=0
        echo "Replay: Complete. Correct Path: Fail"
        fi
        
    else
        correctPath=0
        replayDone=0
        echo "Replay: Error. Non-zero exit code. Correct Path: Fail"
    fi
    
    
    
done

rm pathLog > /dev/null 2> /dev/null
rm global_trace > /dev/null 2> /dev/null
rm -r PoP_Replay/build > /dev/null 2> /dev/null
rm -r PoP_Replay/sootBin > /dev/null 2> /dev/null
    
echo ""
echo "[replay.sh] Final verdict: "
if [ "$replayDone" == "1" ] && [ "$correctPath" == "1" ]
then 
    echo "[replay.sh] Replay: Complete"
    echo "[replay.sh] Correct Path: Pass"
    final_result=0
elif [ "$replayDone" == "1" ] && [ "$correctPath" == "0" ]
then
    echo "[replay.sh] Replay: Complete"
    echo "[replay.sh] Correct Path: Fail"
    final_result=1
elif [ "$replayDone" == "0" ] && [ "$correctPath" == "0" ]
then
    echo "[replay.sh] Replay: Error. Non-zero exit code "
    echo "[replay.sh] Correct path: Fail"
    final_result=2
else
    echo "UNKNOWN ERROR!! Please contact the TA"
    final_result=4
fi
exit $final_result
