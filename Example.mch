MACHINE           Rooms
/* This B Machine models a simplified room locking system.
*/
SETS              ROOM; STATUS = {locked, unlocked}

VARIABLES         position

INVARIANT         position : ROOM --> STATUS

INITIALISATION    position := ROOM * {locked}

OPERATIONS

  unlock(r) = 
  PRE r : ROOM & position(r) = locked THEN position(r) := unlocked END;

  lock(r) = 
  PRE r : ROOM & position(r) = unlocked THEN position(r) := locked END

END
