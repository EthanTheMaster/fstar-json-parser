#!/bin/bash
# git clone https://github.com/nst/JSONTestSuite.git

for filename in ./JSONTestSuite/test_parsing/*.json; do
    basename=$(basename $filename);
    expected_result=$(echo $basename | cut -d _ -f 1);

    if [[ "$expected_result" == "y" ]]; then
        expected_result="Accept";
    elif [[ "$expected_result" == "n" ]]; then
        expected_result="Reject";
    elif [[ "$expected_result" == "i" ]]; then
        expected_result="Indeterminate";
    else
        expected_result="Unknown";
    fi

    # Run parser executable
    cp $filename ./content.json;
    actual_result=$(../Json_Main.native);
    if [[ $? -ne 0 ]]; then
        # Exception was thrown
        actual_result="Reject";
    elif [[ "$actual_result" == "<INVALID JSON>" ]]; then
        actual_result="Reject"
    else
        actual_result="Accept"
    fi

    if [[ "$actual_result" == "$expected_result" || "$expected_result" == "Indeterminate" ]]; then
        echo "$basename: Expected $expected_result, Got $actual_result, ✅"
    else
        echo "$basename: Expected $expected_result, Got $actual_result, ❌"
    fi
done