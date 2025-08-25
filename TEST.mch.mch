MACHINE Library
SETS
  BOOK;
  STATUS = {available, borrowed}

VARIABLES
  books,           /* 已纳入系统管理的书目集合 */
  inventory,       /* books -> NAT，总函数：每本书的库存数量 */
  status           /* books -> STATUS，总函数：每本书的状态 */

INVARIANT
  books ⊆ BOOK &
  inventory ∈ books → NAT &
  status ∈ books → STATUS &
  dom(inventory) = books &
  dom(status)    = books &
  /* 状态与库存一致性：>0 则 available；=0 则 borrowed */
 !(b).( b : books =>
       ( (status(b) = available <=> inventory(b) > 0) &
         (status(b) = borrowed  <=> inventory(b) = 0) ) )

INITIALISATION
  books     := {} ||
  inventory := {} ||
  status    := {}

OPERATIONS

  /* 新增一本尚未纳入系统的书，并指定初始库存（可为 0） */
  add_new_book(bb, qty) =
    PRE bb ∈ BOOK & bb ∉ books & qty ∈ NAT
    THEN
      books     := books ∪ {bb} ||
      inventory := inventory <+ { bb |-> qty } ||
      IF qty = 0 THEN
        status := status <+ { bb |-> borrowed }
      ELSE
        status := status <+ { bb |-> available }
      END
    END;

  /* 删除一本书：仅当库存为 0 才能删除 */
  remove_book(bb) =
    PRE bb ∈ books & inventory(bb) = 0
    THEN
      books     := books \ {bb} ||
      inventory := {bb} <<| inventory ||
      status    := {bb} <<| status
    END;

  /* 借出一本：库存至少为 1；借出后若变为 0，状态切到 borrowed */
borrow_copy(bb) =
  PRE bb ∈ books & inventory(bb) ≥ 1
  THEN
    inventory(bb) := inventory(bb) - 1 ||
    IF inventory(bb) - 1 = 0 THEN
      status(bb) := borrowed
    ELSE
      status(bb) := available
    END
  END;

dec_inventory(bb, delta) =
  PRE bb ∈ books & delta ∈ NAT1 & inventory(bb) ≥ delta
  THEN
    inventory(bb) := inventory(bb) - delta ||
    IF inventory(bb) - delta = 0 THEN
      status(bb) := borrowed
    ELSE
      status(bb) := available
    END
  END;

  /* 归还一本：库存 +1，状态设为 available */
  return_copy(bb) =
    PRE bb ∈ books
    THEN
      inventory(bb) := inventory(bb) + 1 ||
      status(bb)    := available
    END;

  /* 增加库存（批量入库）：正整数 */
  inc_inventory(bb, delta) =
    PRE bb ∈ books & delta ∈ NAT1
    THEN
      inventory(bb) := inventory(bb) + delta ||
      status(bb)    := available
    END



END