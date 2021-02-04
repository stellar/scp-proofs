red=`tput setaf 1`
green=`tput setaf 2`
reset=`tput sgr0`

# This shell script simply checks if there is any output.
# When the Ivy interpretor is not happy, it outputs something like
# "network.ivy: line 52: error: assumption failed"
# to stdout.
# This shell script simply checks that.

echo "======================================"
echo "The following cases should all succeed"
echo "======================================"

for shouldSucceed in tests/succeed/*; do
    if [[ $(./nomination < $shouldSucceed) ]]; then
        echo "${red}$shouldSucceed failed unexpectedly${reset}"
    else
        echo "${green}$shouldSucceed ran as expected${reset}"
    fi
done

echo "==============================================================="
echo "The following cases should all fail due to invariant violations"
echo "==============================================================="

for shouldFail in tests/fail/*; do
    if [[ $(./nomination < $shouldFail) ]]; then
        echo "${green}$shouldFail failed as expected${reset}"
    else
        echo "${red}$shouldFail succeeded unexpectedly${reset}"
    fi
done
