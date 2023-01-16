all:
	$(MAKE) -C aam
	$(MAKE) -C fnd

clean:
	$(MAKE) -C aam clean
	$(MAKE) -C fnd clean

.PHONY: all clean
