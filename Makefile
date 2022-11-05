.PHONY: run-docker

run-docker:
	$(eval IMAGE := mikinglang/miking:latest-alpine)
	$(eval RUNTIMENAME := lr-parsing-test)
	$(eval PWD := $(shell pwd))
	docker run --name $(RUNTIMENAME)     \
	           --hostname $(RUNTIMENAME) \
	           --rm -it                  \
	           -v $(PWD):/mnt:ro         \
	           $(IMAGE) bash
