set -ex

while true; do
    echo "================================================================"
    date
    time python3 scripts/analyze-external-calls.py external-call-use.json
    sleep "$1"
done

