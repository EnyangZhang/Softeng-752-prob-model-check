MACHINE Library

SETS BOOK;BOOK_STATUS={available,booked,borrowed};MEMBER;BOOK_NAME;ADMIN

VARIABLES books,book_catalogue,book_status,members,inventory,book_name,own_book,admins/*,waiting*/

CONSTANTS limit, borrow_limit

PROPERTIES limit=4 & borrow_limit=1

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
 !(mm).(mm:members=>card(own_book[{mm}])<= borrow_limit)
/* waiting:book_name+->seq(MEMBER)&
 dom(waiting)=book_name*/

INITIALISATION
 admins:={};
 books:={};
 book_status:=BOOK*{available};
 book_name:={};
 book_catalogue:={};
 members:={};
 own_book:={};
 inventory:={}

OPERATIONS
 addBookName(bn,ad) = PRE bn:BOOK_NAME & bn/:book_name & ad:ADMIN & ad:admins THEN book_name:=book_name\/{bn} || inventory:=inventory\/{bn|->0} END;//增加admin

 deleteBookName(bn,ad) = PRE bn:book_name & inventory(bn)=0 & bn/:ran(book_catalogue) & ad:admins THEN book_name:=book_name-{bn} || inventory:=inventory-{bn|->inventory(bn)} END;//增加admin,并且不仅inventory需要=0，也不能有人借走了书，此时inventory也是0，这时也不能删除。

 incInventory(bb,bn,ad) = PRE bb:BOOK & bb/:books & (bb|->bn)/:book_catalogue & bn:BOOK_NAME & bn:book_name & inventory(bn)<limit & ad:admins THEN books:=books\/{bb} ; inventory(bn):=inventory(bn)+1 ; book_catalogue:=book_catalogue\/{bb|->bn} END;//增加admin

 decInventory(bb,bn,ad) = PRE bb:books & (bb|->bn):book_catalogue & inventory(bn)>0 &  bn:book_name & ad:admins & bb/:ran(own_book) THEN inventory(bn):=inventory(bn)-1 ; books:=books-{bb} ; book_catalogue:=book_catalogue-{bb|->bn} END;//增加admin, 减少书量的时候bb不能是被借走或者booked状态。

 addMember(mm,ad) = PRE mm:MEMBER & mm/:members & ad:admins THEN members:=members\/{mm} END;//增加admin

 deleteMember(mm,ad) = PRE mm:members & card({mm}<|own_book)=0 & ad:admins THEN members:=members-{mm} END;//检查member身上有没有书， 增加admin

 addAdmin(ad) = PRE ad:ADMIN & ad/:admins THEN admins:=admins\/{ad} END;//增加管理员。管理员的增加与减少其实应该有更高权限的人来做， 但是这个系统的scope就到此为止所以管理员的增减就不做权限的限制

 deleteAdmin(ad) = PRE ad:admins THEN admins:=admins-{ad} END;//减少管理员

 /*borrowBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb):BOOK_STATUS-{borrowed} & inventory(bn)>0 THEN book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1 || own_book:=own_book\/{mm|->bb} END; //需要能borow自己book 不是别人book的*/

 borrowBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & inventory(bn)>0 THEN
 SELECT book_status(bb)=available & card(own_book[{mm}]) < borrow_limit
  THEN book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1 || own_book:=own_book\/{mm|->bb}
 WHEN book_status(bb)=booked & (mm|->bb):own_book
  THEN book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1
  END
 END;//当avaiable时，mm可以borrow；当booked且booed的书是mmbooked时，mm也可以borrow。available时，增加own_book。booked时，检查own_book是否是mm对应bb，不增加duplicated的own_book。增加借available书的时候，有borrowlimit

 returnBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=borrowed & (mm|->bb):own_book THEN book_status(bb):=available || inventory(bn):=inventory(bn)+1 || own_book:=own_book-{mm|->bb} END;//return 之后删掉拥有关系 return 也需要return 自己的书
 
 reserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=available & inventory(bn)>0 & card(own_book[{mm}]) < borrow_limit THEN book_status(bb):=booked || own_book:=own_book\/{mm|->bb} END;
//预约书会增加预约书的关系

 withdrawReserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=booked & inventory(bn)>0 & (mm|->bb):own_book THEN book_status(bb):=available || own_book:=own_book-{mm|->bb} END
//取消预定也会删除member的拥有书的关系
 
 
END

