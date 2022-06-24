all:
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Refl.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Square/Base.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Sym/Base.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Pi/Transport/Lift.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Pi/Transport/Ulift.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Arrow/Transport.agda
	/usr/bin/time --format='Elapsed time: %E\n' agda HOTT/Everything.agda
