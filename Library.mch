MACHINE Library
SETS BOOK;BOOK_STATUS={available,booked,borrowed};MEMBER;BOOK_NAME

VARIABLES books,book_catalogue,book_status,members,inventory,book_name

CONSTANTS limit

PROPERTIES limit=4

INVARIANT
 books:POW(BOOK)&
 book_name:POW(BOOK_NAME)&
 book_catalogue:BOOK+->BOOK_NAME&
 book_status:BOOK-->BOOK_STATUS&
 members:POW(MEMBER)&
 inventory:book_name-->NAT&
 dom(inventory)=book_name&
 !(x).(x:dom(inventory)=>(inventory(x)<=limit))
 
//inventory中的book在入库之前可能不需要inventory的数字
//如果bb不在books里，那么对于所有books在inventory里不能有映射
INITIALISATION 
 books:={};
 book_status:=BOOK*{available};
 book_name:={};
 book_catalogue:={};
 members:={};
 inventory:={}
OPERATIONS
 addBookName(bn) = PRE bn:BOOK_NAME & bn/:book_name THEN book_name:=book_name\/{bn}||inventory:=inventory\/{bn|->0} END;

 deleteBookName(bn) = PRE bn:book_name & inventory(bn)=0 THEN book_name:=book_name-{bn}||inventory:=inventory-{bn|->inventory(bn)} END;

 incInventory(bb,bn) = PRE bb:BOOK & bb/:books & (bb|->bn)/:book_catalogue & bn:BOOK_NAME & bn:book_name & inventory(bn)<limit THEN books:=books\/{bb};inventory(bn):=inventory(bn)+1;book_catalogue:=book_catalogue\/{bb|->bn} END;

 decInventory(bb,bn) = PRE bb:books & (bb|->bn):book_catalogue & inventory(bn)>0 &  bn:book_name THEN inventory(bn):=inventory(bn)-1;books:=books-{bb};book_catalogue:=book_catalogue-{bb|->bn} END;

  addMember(mm) = PRE mm:MEMBER & mm/:members THEN members:=members\/{mm} END;

 deleteMember(mm) = PRE mm:MEMBER & mm:members THEN members:=members-{mm}END;

 borrowBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn) : book_catalogue &  bn:book_name & book_status(bb) = available & inventory(bn) > 0 THEN book_status(bb):=borrowed||inventory(bn):=inventory(bn)-1 END; //需要配合reserve

 returnBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn) : book_catalogue &  bn:book_name & book_status(bb) = borrowed THEN book_status(bb):=available||inventory(bn):=inventory(bn)+1 END;
 
 reserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn) : book_catalogue & bn:book_name & book_status(bb) = available & inventory(bn) > 0 THEN book_status(bb):=booked END;

 withdrawReserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn) : book_catalogue & bn:book_name & book_status(bb) = booked & inventory(bn) > 0 THEN book_status(bb):=available END

END

