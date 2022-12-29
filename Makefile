.PHONY: run-docker

test:
	$(eval UID := $(shell if [ -z "$$SUDO_UID" ]; then id -u; else echo "[$$SUDO_UID]"; fi))
	$(eval GID := $(shell if [ -z "$$SUDO_GID" ]; then id -g; else echo "[$$SUDO_GID]"; fi))
	@echo "UID = \"$(UID)\""
	@echo "GID = \"$(GID)\""

run-docker:
	$(eval IMAGE := mikinglang/miking:latest-alpine)
	$(eval RUNTIMENAME := lr-parsing-test)
	$(eval PWD := $(shell pwd))
	docker run --name $(RUNTIMENAME)     \
	           --hostname $(RUNTIMENAME) \
	           --user $(UID):$(GID)      \
	           --rm -it                  \
	           -v $(PWD):/mnt:ro         \
	           $(IMAGE) bash
