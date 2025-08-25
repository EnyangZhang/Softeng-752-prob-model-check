MACHINE Library
SETS BOOK;BOOK_STATUS={available,booked,borrowed};MEMBER

VARIABLES books,book_status,members,inventory

CONSTANTS limit

PROPERTIES limit=4

INVARIANT
 books:POW(BOOK)&
 book_status:BOOK-->BOOK_STATUS&
 members:POW(MEMBER)&
 inventory:books-->NAT&
 dom(inventory)=books&
 !(x).(x:dom(inventory)=>(inventory(x)<=limit))
//inventory中的book在入库之前可能不需要inventory的数字
//如果bb不在books里，那么对于所有books在inventory里不能有映射
INITIALISATION 
 books:={};
 book_status:=BOOK*{available};
 members:={};
 inventory:={}
OPERATIONS
 addbook(bb) = PRE bb:BOOK & bb/:books THEN books:=books\/{bb}||inventory:=inventory \/ {bb |-> 0} END;//关于并行的constrain

 deletebook(bb) = PRE bb:books & inventory<|{bb}== THEN books:=books-{bb}||inventory:=inventory -{bb |-> inventory(bb)} END; // 是不是应该是 bb<: books, 这里应该限制inventory 必须是0才能删除， 不应该直接删除

 addinventory(bb) = PRE bb:books & inventory(bb) < limit THEN  inventory := inventory <+ { bb |-> inventory(bb) + 1 } END;

 addmember(mm) = PRE mm:MEMBER & mm/: members THEN members:=members\/{mm} END;

 deletemember(mm) = PRE mm:MEMBER & mm:members THEN members:=members-{mm}END

END

