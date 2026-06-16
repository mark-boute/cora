#!/bin/sh

BLUE_BOLD='\033[1;34m'
GREY='\033[0;90m'
NC='\033[0m'

# Initialize counters
YES_COUNT=0
MAYBE_COUNT=0
FAIL_COUNT=0
CURRENT_INDEX=0
TOTAL_FILES=0

run_file() {
    ((CURRENT_INDEX++))
    REMAINING=$((TOTAL_FILES - CURRENT_INDEX))

    # --- CLEAR LINE AND OVERWRITE ---
    # \r moves cursor to start, \033[K clears the rest of the line to prevent ghost text
    printf "\r\033[K${BLUE_BOLD}Progress:${NC} ✅ %d  ❌ %d  ❓ %d  |  ⏳ %d remaining" \
        "$YES_COUNT" "$FAIL_COUNT" "$MAYBE_COUNT" "$REMAINING" > /dev/tty

    # Remove or comment out the "Running: <file>" print statement, 
    # because printing text with newlines will break the single-line layout!
    # printf "${BLUE_BOLD}Running:${NC} %s\n" "$1"
    
    start=$(date +%s%3N)
    output=$(GRADLE_OPTS="-Xmx8g -Xms2g" ./gradlew run -q --args="../$1")
    end=$(date +%s%3N)
    
    printf "%s\n" "$output"
    result=$(echo "$output" | head -n 1)
    
    case "$result" in
        YES*)   ((YES_COUNT++)) ;;
        MAYBE*) ((MAYBE_COUNT++)) ;;
        *)      ((FAIL_COUNT++)) ;;
    esac

    # (Optional) If you want the final progress update to cleanly reflect 
    # the last file's result immediately before the summary block:
    REMAINING=$((TOTAL_FILES - CURRENT_INDEX))
    printf "\r\033[K${BLUE_BOLD}Progress:${NC} ✅ %d  ❌ %d  ❓ %d  |  ⏳ %d remaining" \
        "$YES_COUNT" "$FAIL_COUNT" "$MAYBE_COUNT" "$REMAINING" > /dev/tty
}

case "$1" in
    --all)
        if [ -d "$2" ]; then
            TOTAL_FILES=$(find "$2" -maxdepth 1 -type f | wc -l)
            
            for f in "$2"/*; do
                [ -f "$f" ] && run_file "$f"
            done
            
            # --- TERMINAL ONLY PRINT ---> /dev/tty ---
            printf "${BLUE_BOLD}Final Progress:${NC} ✅ %d  ❌ %d  ❓ %d  |  ⏳ 0 remaining\n" \
                "$YES_COUNT" "$FAIL_COUNT" "$MAYBE_COUNT" > /dev/tty
            echo "--------------------------------------" > /dev/tty

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
            TOTAL_FILES=1
            run_file "$*"
        fi
        ;;
esac