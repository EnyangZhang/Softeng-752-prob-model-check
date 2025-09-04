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
 !(mm).(mm:members=>card(own_book[{mm}])+card({ bn | bn:book_name & mm : ran(waiting(bn)) })<=borrow_limit)& //waitinglist 也占用用户borrow的limit
 waiting:book_name+->seq(MEMBER)&
 dom(waiting)=book_name&
 !(bn)·(bn:book_name=>card(ran(waiting(bn))) = size(waiting(bn)))& //对每个书名 bn，等待队列 waiting(bn) 里没有重复的人。
 !(bn).( bn : book_name => ran(waiting(bn)) <: members ) //waiting 里只能有现有会员

DEFINITIONS
  /* 借阅上限始终成立（把不变式写成 LTL） */
  ASSERT_LTL1 == "G({!(mm).(mm : members => card(own_book[{mm}]) <= borrow_limit)})";

  /* available 的副本不能同时被占用（own_book 的值域里没有 available 的书） */
  ASSERT_LTL2 == "G({!(bb).(bb : books & book_status(bb)=available => bb /: ran(own_book))})";

  /* 目录与集合的粘合关系始终成立 */
  ASSERT_LTL3 == "G({dom(book_catalogue)=books & ran(book_catalogue) <: book_name})";

  /* 预定执行后：这一步把至少一本原本 available 的册子变成了 booked。 */
//  ASSERT_LTL4 == "G([reserveBook] => X{#(mm,bb).((mm |-> bb) : own_book & book_status(bb)=booked) > 0})";
  ASSERT_LTL4 == "G([reserveBook] => BA({ card({bb | bb : books & book_status$0(bb)=available & book_status(bb)=booked}) > 0 }))";

  /* 借书执行后：确保这一步确实把某本从 available/booked 变为 borrowed */
  ASSERT_LTL5 == "G([borrowBook] => BA({ #(mm,bb,bn).( mm:members & bb:books & bn:book_name & (bb|->bn):book_catalogue & ( (book_status$0(bb)=available & book_status(bb)=borrowed & inventory(bn)=inventory$0(bn)-1 & (mm|->bb):own_book & not((mm|->bb):own_book$0)) or (book_status$0(bb)=booked & book_status(bb)=borrowed & inventory(bn)=inventory$0(bn)-1 & (mm|->bb):own_book & (mm|->bb):own_book$0 ) ) ) }))";

  /* 还书执行后：归还发生时，对应书名 bn 的 inventory 必须 +1，无论之后是否立刻变 booked。 */
  ASSERT_LTL6 == "G([returnBook] => BA({ #(bb,bn).( bb:books & (bb|->bn):book_catalogue & book_status$0(bb)=borrowed & book_status(bb):{available,booked} & inventory(bn)=inventory$0(bn)+1 ) }))";

/* 7a 若该书名前态有人在等（且存在额度未满者），新加的那本后态必须是 booked；库存不作额外约束 */
  ASSERT_LTL7a == "G([incInventory] => BA({ #bn,bb.( (bb|->bn):book_catalogue & not((bb|->bn):book_catalogue$0) & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => book_status(bb)=booked ) ) }))";

/* 7b 归还：若该书名前态存在可分配者，则归还的这本后态必须是 booked；并且 inventory(bn) = inventory$0(bn) + 1 〔符合“归还加库存”且 booked 不减库存〕 */
  ASSERT_LTL7b == "G([returnBook] => BA({ #bn,bb.( (bb|->bn):book_catalogue & book_status$0(bb)=borrowed & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => ( book_status(bb)=booked & inventory(bn)=inventory$0(bn)+1 ) ) ) }))";

/* 7c 取消预定：若该书名前态存在可分配者，则这本后态仍应是 booked（换人也行）；库存不变〔booked→booked〕 */
  ASSERT_LTL7c == "G([withdrawReserveBook] => BA({ #bn,bb.( (bb|->bn):book_catalogue & book_status$0(bb)=booked & ( #m.( m:ran(waiting$0(bn)) & card(own_book$0[{m}]) < borrow_limit ) => book_status(bb)=booked ) ) }))";

ASSERTIONS
/* A1' 库存=可用或已预定的副本数（按你们“booked 不减库存”的语义） */
 !(bn).( bn : book_name =>
  inventory(bn)=card({ bb | bb : books & (bb |-> bn) : book_catalogue & book_status(bb) : {available, booked} }));

/* A1b 借出数 = 总册数 − 库存（守恒律） */
 !(bn).( bn : book_name =>
  card({ bb | bb : books & (bb |-> bn) : book_catalogue & book_status(bb) = borrowed }) =
  card({ bb | bb : books & (bb |-> bn) : book_catalogue }) - inventory(bn));

/* A2' 非可用状态必须且仅能被一个成员占用（唯一占用） */
 !(bb).( bb : books & book_status(bb) : {booked, borrowed} =>
        card({ mm | (mm |-> bb) : own_book }) = 1 );

/* A3 可用副本绝不出现在占用关系中（强于 “/∈ ran(own_book)” 的计数版） */
 !(bb).( bb : books & book_status(bb) = available =>
        card({ mm | (mm |-> bb) : own_book }) = 0 );

/* A4 占用关系只涉及“已注册成员/在库副本” */
 dom(own_book) <: members;
 ran(own_book) <: books;

/* A5 等待队列的元素都是成员（类型安全，便于在报告里说明） */
 !(bn).( bn : book_name => ran(waiting(bn)) <: members );

/* A6 已分配（booked/borrowed）的那本书，其对应书名的等待队列里不应再包含该成员（自动出队的正确性） */
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
 addBookName(bn,ad) = PRE bn:BOOK_NAME & bn/:book_name & ad:ADMIN & ad:admins THEN book_name:=book_name\/{bn} || inventory:=inventory\/{bn|->0} || waiting:=waiting\/{bn|->[]} END;//增加admin, 增加空的队列

 deleteBookName(bn,ad) = PRE bn:book_name & inventory(bn)=0 & bn/:ran(book_catalogue) & ad:admins THEN book_name:=book_name-{bn} || inventory:=inventory-{bn|->inventory(bn)} || waiting:={bn}<<|waiting END;//增加admin,并且不仅inventory需要=0，也不能有人借走了书，此时inventory也是0，这时也不能删除。

 incInventory(bb,bn,ad) = PRE bb:BOOK & bb/:books & (bb|->bn)/:book_catalogue & bn:BOOK_NAME & bn:book_name & inventory(bn)<limit & ad:admins THEN books:=books\/{bb} ; inventory(bn):=inventory(bn)+1 ; book_catalogue:=book_catalogue\/{bb|->bn} ;//增加admin，waitinglist 中有人在等， 但是新加了一本书，waitinglist里的人也会将新加的书进行自动book
 /* ② 根据等待队列决定新册状态 */
  IF bn:dom(waiting) & waiting(bn)/=[] THEN 
   VAR m0,rest IN 
    m0:=first(waiting(bn)) ; 
    rest:=tail(waiting(bn)) ;

    IF card(own_book[{m0}])<borrow_limit THEN 
     /* 分配给队首 m0：设为 booked，建立占用关系，弹出队首 */
     book_status(bb):= booked ; 
     own_book:=own_book\/{m0|->bb} ; 
     waiting:=waiting<+{bn|->rest}
    ELSE 
     /* 队首已达上限：bb 仍为 available，队列保持不变 */
     book_status(bb):=available 
    END 
   END

  ELSE
   /* 无等待者：正常入库为 available */
   book_status(bb):=available
  END
 END;

 decInventory(bb,bn,ad) = PRE bb:books & (bb|->bn):book_catalogue & inventory(bn)>0 & bn:book_name & ad:admins & bb/:ran(own_book) THEN inventory(bn):=inventory(bn)-1 ; books:=books-{bb} ; book_catalogue:=book_catalogue-{bb|->bn} END;//增加admin, 减少书量的时候bb不能是被借走或者booked状态。

 addMember(mm,ad) = PRE mm:MEMBER & mm/:members & ad:admins THEN members:=members\/{mm} END;//增加admin

 deleteMember(mm,ad) = PRE mm:members & card({mm}<|own_book)=0 & ad:admins & !(bn).(bn:book_name=>mm/:ran(waiting(bn))) THEN members:=members-{mm} END;//检查member身上有没有书， 增加admin

 addAdmin(ad) = PRE ad:ADMIN & ad/:admins THEN admins:=admins\/{ad} END;//增加管理员。管理员的增加与减少其实应该有更高权限的人来做， 但是这个系统的scope就到此为止所以管理员的增减就不做权限的限制

 deleteAdmin(ad) = PRE ad:admins THEN admins:=admins-{ad} END;//减少管理员

 borrowBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & inventory(bn)>0 THEN
  SELECT book_status(bb)=available & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))}) < borrow_limit THEN 
   book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1 || own_book:=own_book\/{mm|->bb}
  WHEN book_status(bb)=booked & (mm|->bb):own_book THEN 
   book_status(bb):=borrowed || inventory(bn):=inventory(bn)-1
  END
 END;//当avaiable时，mm可以borrow；当booked且booed的书是mmbooked时，mm也可以borrow。available时，增加own_book。booked时，检查own_book是否是mm对应bb，不增加duplicated的own_book。增加借available书的时候，有borrowlimit

 returnBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=borrowed & (mm|->bb):own_book THEN book_status(bb):=available || inventory(bn):=inventory(bn)+1 || own_book:=own_book-{mm|->bb} ;
      /* ② 自动分配给等待队列首成员（若有且未超额） */
  IF bn:dom(waiting) & waiting(bn) /= [] THEN
   VAR m0,rest IN
    m0:=first(waiting(bn)) ;
    rest:=tail(waiting(bn)) ;

    IF card(own_book[{m0}])<borrow_limit THEN
     book_status(bb):=booked ;
     own_book:=own_book\/{m0|->bb} ;
     waiting:=waiting<+{bn|->rest}
/*    ELSE
*/     /* 队首已超额：队列保持不变，您也可改为 rest^[m0] 放队尾 */
/*     waiting:=waiting<+{bn|->waiting(bn)}*/
    END

   END
  END
 END;//return 之后删掉拥有关系 return 也需要return 自己的书
 
 reserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=available & inventory(bn)>0 & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))})< borrow_limit THEN book_status(bb):=booked || own_book:=own_book\/{mm|->bb} END;
//预约书会增加预约书的关系

 withdrawReserveBook(bb,bn,mm) = PRE mm:members & bb:books & (bb|->bn):book_catalogue & bn:book_name & book_status(bb)=booked & inventory(bn)>0 & (mm|->bb):own_book THEN book_status(bb):=available || own_book:=own_book-{mm|->bb} ;
  /* ② 自动分配等待队列 */
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
//取消预定也会删除member的拥有书的关系

 addWaiting(bn,mm) = PRE mm : members & bn:book_name & not(#(bb).((bb|->bn):book_catalogue & book_status(bb)=available)) & card(own_book[{mm}])+card({bn1|bn1:book_name & mm:ran(waiting(bn1))})<borrow_limit & mm/:ran(waiting(bn)) & not( #(bb).( (mm |-> bb) : own_book & (bb |-> bn) : book_catalogue ) ) THEN waiting:=waiting<+{bn|->(waiting(bn)^[mm])} END;
 
 removeWaiting(bn,mm) = PRE bn:book_name & mm:members & mm:ran(waiting(bn)) THEN
  VAR x,y,s IN
   x:=waiting(bn);          /* 当前等待序列            */
   s:=size(x);              /* 长度                     */
   y:=[];                   /* 结果序列（初始为空）     */
   WHILE s>0 DO
    IF first(x)/=mm THEN
     y:=y^[first(x)]  /* 把不是 mm 的元素追加到 y */
    END;
    x:=tail(x);            /* 去掉已检查的首元素       */
    s:=size(x)             /* 更新长度，用作变式       */
    INVARIANT y:seq(MEMBER) & card(y)<=card(waiting(bn))    /* 始终不比原序列长   */
    VARIANT s
   END;
  /* 写回新的等待序列；保持键 bn 存在 */
   waiting:=waiting<+{bn|->y}
  END
 END

END

