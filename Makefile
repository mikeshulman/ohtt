all:
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Refl.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Square/Base.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Square/Equality.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Sym/Base.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Pi/Transport.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Everything.agda
