/*The DEFAULT_SETSIZE sets to 2 and MAXINT sets to 10 as the NAT is been used*/
MACHINE Library

SETS BOOK;BOOK_STATUS={available,booked,borrowed};MEMBER;BOOK_NAME;ADMIN

VARIABLES books,book_catalogue,book_status,members,inventory,book_name,own_book,admins,waiting

CONSTANTS limit, borrow_limit

PROPERTIES limit=4 & borrow_limit=2

INVARIANT
 admins:POW(ADMIN)&
 books:POW(BOOK)&
 book_name:POW(BOOK_NAME)&
 book_catalogue:BOOK+->BOOK_NAME&
 book_status:BOOK-->BOOK_STATUS&
 members:POW(MEMBER)&
 own_book:MEMBER<->BOOK&
 inventory:book_name-->NAT&
 dom(inventory)=book_name&
 !(bn).(bn:dom(inventory)=>(inventory(bn)<=limit))&
 !(mm).(mm:members=>card(own_book[{mm}])+card({bn|bn:book_name&mm:ran(waiting(bn))})<=borrow_limit)& 
 waiting:book_name+->seq(MEMBER)&
 dom(waiting)=book_name&
 !(bn)·(bn:book_name=>card(ran(waiting(bn)))=size(waiting(bn)))&
 !(bn).(bn:book_name=>ran(waiting(bn))<:members) 

DEFINITIONS
  ASSERT_LTL1 == "G({!(mm).(mm : members => card(own_book[{mm}]) <= borrow_limit)})";

  ASSERT_LTL2 == "G({!(bb).(bb : books & book_status(bb)=available => bb /: ran(own_book))})";

  ASSERT_LTL3 == "G({dom(book_catalogue)=books & ran(book_catalogue) <: book_name})";

  ASSERT_LTL4 == "G([reserveBook] => BA({ card({bb | bb : books & book_status$0(bb)=available & book_status(bb)=booked}) > 0 }))";

  ASSERT_LTL5 == "G([borrowBook] => BA({ #(mm,bb,bn).( mm:members & bb:books & bn:book_name & (bb|->bn):book_catalogue & ( (book_status$0(bb)=available & book_status(bb)=borrowed & inventory(bn)=inventory$0(bn)-1 & (mm|->bb):own_book & not((mm|->bb):own_book$0)) or (book_status$0(bb)=booked & book_status(bb)=borrowed & inventory(bn)=inventory$0(bn)-1 & (mm|->bb):own_book & (mm|->bb):own_book$0 ) ) ) }))";

  ASSERT_LTL6 == "G([returnBook] => BA({ #(bb,bn).( bb:books & (bb|->bn):book_catalogue & book_status$0(bb)=borrowed & book_status(bb):{available,booked} & inventory(bn)=inventory$0(bn)+1 ) }))";

  ASSERT_LTL7a == "G([incInventory] => BA({ #bn,bb.( (bb|->bn):book_catalogue & not((bb|->bn):book_catalogue$0) & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => book_status(bb)=booked ) ) }))";

  ASSERT_LTL7b == "G([returnBook] => BA({ #bn,bb.( (bb|->bn):book_catalogue & book_status$0(bb)=borrowed & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => ( book_status(bb)=booked & inventory(bn)=inventory$0(bn)+1 ) ) ) }))";

  ASSERT_LTL7c == "G([withdrawReserveBook] => BA({ #bn,bb.( (bb|->bn):book_catalogue & book_status$0(bb)=booked & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => book_status(bb)=booked ) ) }))";

ASSERTIONS
/* A1 */
 !(bn).( bn : book_name =>
  inventory(bn)=card({ bb | bb : books & (bb |-> bn) : book_catalogue & book_status(bb) : {available, booked} }));

/* A1b */
 !(bn).( bn : book_name =>
  card({ bb | bb : books & (bb |-> bn) : book_catalogue & book_status(bb) = borrowed }) =
  card({ bb | bb : books & (bb |-> bn) : book_catalogue }) - inventory(bn));

/* A2 */
 !(bb).( bb : books & book_status(bb) : {booked, borrowed} =>
        card({ mm | (mm |-> bb) : own_book }) = 1 );

/* A3 */
 !(bb).( bb : books & book_status(bb) = available =>
        card({ mm | (mm |-> bb) : own_book }) = 0 );

/* A4 */
 dom(own_book) <: members;
 ran(own_book) <: books;

/* A5 */
 !(bn).( bn : book_name => ran(waiting(bn)) <: members );

/* A6 */
 !(bn,bb,mm).((bb |-> bn) : book_catalogue & (mm |-> bb) : own_book => mm /: ran(waiting(bn)))

INITIALISATION
 admins:={};
 books:={};
 book_status:=BOOK*{available};
 book_name:={};
 book_catalogue:={};
 members:={};
 own_book:={};
 inventory:={};
 waiting:={}

OPERATIONS
 addBookName(bn,ad) = PRE bn:BOOK_NAME & bn/:book_name & ad:ADMIN & ad:admins THEN book_name:=book_name\/{bn} || inventory:=inventory\/{bn|->0} || waiting:=waiting\/{bn|->[]} END;

 deleteBookName(bn,ad) = PRE bn:book_name & inventory(bn)=0 & bn/:ran(book_catalogue) & ad:admins & waiting(bn)=[] THEN book_name:=book_name-{bn} || inventory:=inventory-{bn|->inventory(bn)} || waiting:={bn}<<|waiting END;

 incInventory(bb,bn,ad) = PRE bb:BOOK & bb/:books & (bb|->bn)/:book_catalogue & bn:BOOK_NAME & bn:book_name & inventory(bn)<limit & ad:admins THEN books:=books\/{bb} ; inventory(bn):=inventory(bn)+1 ; book_catalogue:=book_catalogue\/{bb|->bn} ;
  IF bn:dom(waiting) & waiting(bn)/=[] THEN 
   VAR m0,rest IN 
    m0:=first(waiting(bn)) ; 
    rest:=tail(waiting(bn)) ;

    IF card(own_book[{m0}])<borrow_limit THEN 
     book_status(bb):= booked ; 
     own_book:=own_book\/{m0|->bb} ; 
     waiting:=waiting<+{bn|->rest}
    ELSE 
     book_status(bb):=available 
    END 
   END

  ELSE
   book_status(bb):=available
  END
 END;

 decInventory(bb,bn,ad) = PRE bb:books & (bb|->bn):book_catalogue & inventory(bn)>0 & bn:book_name & ad:admins & bb/:ran(own_book) THEN inventory(bn):=inventory(bn)-1 ; books:=books-{bb} ; book_catalogue:=book_catalogue-{bb|->bn} END;

 addMember(mm,ad) = PRE mm:MEMBER & mm/:members & ad:admins THEN members:=members\/{mm} END;

 deleteMember(mm,ad) = PRE mm:members & card({mm}<|own_book)=0 & ad:admins & !(bn).(bn:book_name=>mm/:ran(waiting(bn))) THEN members:=members-{mm} END;

 addAdmin(ad) = PRE ad:ADMIN & ad/:admins THEN admins:=admins\/{ad} END;

 deleteAdmin(ad) = PRE ad:admins THEN admins:=admins-{ad} END;

 borrowBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & inventory(bn)>0 THEN
  SELECT book_status(bb)=available & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))}) < borrow_limit THEN 
   book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1 || own_book:=own_book\/{mm|->bb}
  WHEN book_status(bb)=booked & (mm|->bb):own_book THEN 
   book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1
  END
 END;

 returnBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=borrowed & (mm|->bb):own_book THEN book_status(bb):=available || inventory(bn):=inventory(bn)+1 || own_book:=own_book-{mm|->bb} ;
  IF bn:dom(waiting) & waiting(bn) /= [] THEN
   VAR m0,rest IN
    m0:=first(waiting(bn)) ;
    rest:=tail(waiting(bn)) ;

    IF card(own_book[{m0}])<borrow_limit THEN
     book_status(bb):=booked ;
     own_book:=own_book\/{m0|->bb} ;
     waiting:=waiting<+{bn|->rest}
    END

   END
  END
 END;
 
 reserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=available & inventory(bn)>0 & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))})< borrow_limit THEN book_status(bb):=booked || own_book:=own_book\/{mm|->bb} END;

 withdrawReserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=booked & inventory(bn)>0 & (mm|->bb):own_book THEN book_status(bb):=available || own_book:=own_book-{mm|->bb} ;
  IF bn:dom(waiting) & waiting(bn)/=[] THEN
   VAR m0,rest IN
    m0:=first(waiting(bn)) ;
    rest:=tail(waiting(bn)) ;

    IF card(own_book[{m0}])<borrow_limit THEN
     book_status(bb):=booked ;
     own_book:=own_book\/{m0|->bb} ;
     waiting:=waiting<+{bn|->rest}
    ELSE
     waiting:=waiting<+{bn|->waiting(bn)}
    END

   END
  END
 END;

 addWaiting(bn,mm) = PRE mm:members & bn:book_name & not(#(bb).((bb|->bn):book_catalogue & book_status(bb)=available)) & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))})<borrow_limit & mm/:ran(waiting(bn)) & not(#(bb).((mm|->bb):own_book & (bb|->bn):book_catalogue)) THEN waiting:=waiting<+{bn|->(waiting(bn)^[mm])} END;
 
 removeWaiting(bn,mm) = PRE bn:book_name & mm:members & mm:ran(waiting(bn)) THEN
  VAR x,y,s IN
   x:=waiting(bn);        
   s:=size(x);             
   y:=[];                  
   WHILE s>0 DO
    IF first(x)/=mm THEN
     y:=y^[first(x)]  
    END;
    x:=tail(x);            
    s:=size(x)            
    INVARIANT y:seq(MEMBER) & card(y)<=card(waiting(bn))   
    VARIANT s
   END;
   waiting:=waiting<+{bn|->y}
  END
 END

END

