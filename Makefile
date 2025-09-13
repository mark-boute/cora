DIST_DIR := ./app/build/distributions

.PHONY: all
all:
	./gradlew clean
	./gradlew build --rerun-tasks --no-build-cache --info

define path_question
	$(eval confirm := $(shell read -p "Do you want to automatically add cora to your path? [y/n] > " -r; echo $$REPLY))
	$(if $(filter y Y,$(confirm)),1)
endef

util_confirm_ask = $(strip $(path_question))

add_to_path:
	$(if $(util_confirm_ask), \
		@echo "User said yes", \
		@echo "User said no" \
	)

install:
	@cd $(DIST_DIR) && unzip -qo app.zip
	@rm -rf $(DIST_DIR)/.cora
	@mkdir -p $(DIST_DIR)/.cora
	@mkdir -p $(DIST_DIR)/.cora/bin
	@cp $(DIST_DIR)/app/bin/app $(DIST_DIR)/.cora/bin/cora
	@cp -R $(DIST_DIR)/app/lib $(DIST_DIR)/.cora
	@echo "Cora was successfully installed at $(DIST_DIR)/.cora."
	@echo "If you would like to run it from anywhere, please add the following line to your bash profile:"
	@echo 'export PATH="$(DIST_DIR)/.cora/bin:$$PATH"'
	@echo "For security reasons, this installation script will not change this file for you."

uninstall:
	@echo "Uninstalling cora..."
	rm -rf $(DIST_DIR)/.cora
	@echo "Done."
	@echo "Note: if you have added $(DIST_DIR)/.cora/bin to your PATH variable, please remove it manually."

run_exp_all:
	cd ./cora_distribution && ./run_exp_all.sh
