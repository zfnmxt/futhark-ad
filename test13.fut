let main (x: i32) = loop acc1 = x for i < 2 do
		      loop acc2 = 0 for j < 2 do
		      	acc2 + x + i

--Warning at test13.fut:2:45-45:
--  Defaulting ambiguous type to i32.
--futhark-ad: entry {i32} main (i32 x_9) = {
--  let {i32 res_10} =
--    loop {i32 acc1_11} = {x_9}
--    for i_12:i32 < 2i32 do {
--      let {i32 loopres_13} =
--        loop {i32 acc2_14} = {0i32}
--        for j_15:i32 < 2i32 do {
--          let {i32 x_16} = add32(x_9, acc2_14)
--          let {i32 loopres_17} = add32(i_12, x_16)
--          in {loopres_17}
--        }
--      in {loopres_13}
--    }
--  in {res_10}
--}
