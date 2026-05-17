#!/usr/bin/env bash

# File paths
RESULTS_DIR=".."
RESULTS_FILE="$RESULTS_DIR/results.txt"
LOG_FILE="$RESULTS_DIR/results.log"
RUN_SCRIPT="./run.sh"

touch "$RESULTS_FILE"
touch "$LOG_FILE"

# Define benchmarks to run (format: "Header:Path")
BENCHMARKS=(
    "# TRS_Standard:../TPDB-ARI/TRS_Standard"
    "# SRS_Standard:../TPDB-ARI/SRS_Standard"
)

# List of folders you already completed, exclude them using:
# benchmark_name/subfolder_name (e.g., TRS_Standard/AG01)
SKIPPED_FOLDERS="

"

for entry in "${BENCHMARKS[@]}"; do
    HEADER="${entry%%:*}"
    BASE_DIR="${entry#*:}"
    PARENT_DIR=$(basename "$BASE_DIR")

    if [ ! -d "$BASE_DIR" ]; then
        echo "Warning: Directory $BASE_DIR not found. Skipping..."
        continue
    fi

    echo "Processing $HEADER..."

    if ! grep -q "^$HEADER" "$RESULTS_FILE"; then
        echo -e "\n$HEADER\n\nSUCCESS / MAYBE or NO / ERROR" >> "$RESULTS_FILE"
    fi

    for subfolder_path in $(ls -d "$BASE_DIR"/*/ 2>/dev/null | sort); do
        subfolder=$(basename "$subfolder_path")
        if echo "$SKIPPED_FOLDERS" | grep -Fqx "$current_target"; then
            echo "  Skipping already completed folder: $current_target"
            continue
        fi

        if grep -q "^- $PARENT_DIR/$subfolder" "$RESULTS_FILE"; then
            echo "  Skipping (already found in results.txt): $PARENT_DIR/$subfolder"
            continue
        fi

        echo "  Running: $PARENT_DIR/$subfolder"

        raw_output=$("$RUN_SCRIPT" --all "$subfolder_path" 2>&1)
        counts_line=$(echo "$raw_output" | tail -n 1 | xargs)        
        formatted_counts=$(echo "$counts_line" | awk '{print $1 " / " $2 " / " $3}')
        
        echo "  ↳ Result: $formatted_counts"
        
        {
            echo ""
            echo "- $PARENT_DIR/$subfolder"
            echo "  $formatted_counts"
        } >> "$RESULTS_FILE"

        {
            echo "================================================================================"
            echo "START BENCHMARK: $PARENT_DIR/$subfolder [$(date '+%Y-%m-%d %H:%M:%S')]"
            echo "================================================================================"
            echo "$raw_output"
            echo "================================================================================"
            echo "END BENCHMARK: $PARENT_DIR/$subfolder"
            echo -e "================================================================================"
            echo ""
        } >> "$LOG_FILE"

    done
done

echo "Benchmarks complete!"
echo "  -> Results saved/updated in $RESULTS_FILE"
echo "  -> Full raw outputs captured in $LOG_FILE"