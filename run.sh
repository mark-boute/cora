#!/bin/sh

BLUE_BOLD='\033[1;34m'
GREY='\033[0;90m'
NC='\033[0m'

# Initialize counters
YES_COUNT=0
MAYBE_COUNT=0
FAIL_COUNT=0

run_file() {
    printf "${BLUE_BOLD}Running:${NC} %s\n" "$1"
    
    start=$(date +%s%3N)
    output=$(./gradlew run -q --args="../$1")
    end=$(date +%s%3N)
    printf "%s\n" "$output"
    result=$(echo "$output" | head -n 1)
    
    case "$result" in
        YES*)   ((YES_COUNT++)) ;;
        MAYBE*) ((MAYBE_COUNT++)) ;;
        *)      ((FAIL_COUNT++)) ;;
    esac

    total_ms=$((end - start))
    seconds=$((total_ms / 1000))
    ms=$((total_ms % 1000))
    
    if [ "$seconds" -gt 0 ]; then
        time_str="${seconds}s and ${ms}ms"
    else
        time_str="${ms}ms"
    fi
    
    printf "${GREY}(Execution time: ${time_str})${NC}\n"
    echo "--------------------------------------"
}

case "$1" in
    --all)
        if [ -d "$2" ]; then
            for f in "$2"/*; do
                [ -f "$f" ] && run_file "$f"
            done
            printf "${BLUE_BOLD}Summary:${NC}\n"
            printf "%-12s / %-12s / %-12s\n" "YES" "MAYBE" "FAIL"
            printf "%-12s   %-12s   %-12s\n" "$YES_COUNT" "$MAYBE_COUNT" "$FAIL_COUNT"
        else
            echo "Error: $2 is not a directory."
            exit 1
        fi
        ;;
    *)
        if [ $# -eq 0 ]; then
            ./gradlew run
        else
            run_file "$*"
        fi
        ;;
esac