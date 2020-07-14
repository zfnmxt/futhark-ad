let main (x: i32) = loop acc = x for i < 3 do acc*x


-- futhark-ad: let {i32 loopres_9} = mul32(x_5, e_7)

--futhark-ad: entry {i32} main (i32 x_5) = {
--  let {i32 res_6} =
--    loop {i32 e_7} = {x_5}
--    for i_8:i32 < 10i32 do {
--      let {i32 loopres_9} = mul32(x_5, e_7)
--      in {loopres_9}
--    }
--  in {res_6}
--}

--body
-- futhark-ad: let {i32 res_6} =
--   loop {i32 e_7} = {x_5}
--   for i_8:i32 < 10i32 do {
--     let {i32 loopres_9} = mul32(x_5, e_7)
--     in {loopres_9}
--   }
-- in {res_6}

--stms
-- fromList ["let {i32 res_6} =\n  loop {i32 e_7} = {x_5}\n  for i_8:i32 < 10i32 do {\n    let {i32 loopres_9} = mul32(x_5, e_7)\n    in {loopres_9}\n  }"]


--Warning at test6.fut:1:42-42:
--  Defaulting ambiguous type to i32.
--futhark-ad: entry {i32} main (i32 x_5, i32 res_adj_21) = {
--  let {i32 x_adj_10} = 0i32
--  let {[2i32]i32 blank_20} = scratch(i32, 2i32)
--  let {i32 res_6, [2i32]i32 res_acc_11} =
--    loop {i32 acc_7, [2i32]i32 res_acc_loop_12} = {x_5, blank_20}
--    for i_8:i32 < 2i32 do {
--      let {i32 loopres_9} = mul32(x_5, acc_7)
--      let {[2i32]i32 copy_13} = copy(res_acc_loop_12)
--      let {bool less_than_zero_14} = slt32(i_8, 0i32)
--      let {bool greater_than_size_15} = sle32(2i32, i_8)
--      let {bool outside_bounds_dim_16} =
--        logor(less_than_zero_14, greater_than_size_15)
--      let {bool outside_bounds_17} = logor(outside_bounds_dim_16, false)
--      let {[2i32]i32 write_19} =
--        -- Branch returns: {[2i32]i32}
--        if outside_bounds_17
--        then {copy_13} else {
--          let {[2i32]i32 write_out_inside_bounds_18} =
--            copy_13 with [i_8] <- loopres_9
--          in {write_out_inside_bounds_18}
--        }
--      in {loopres_9, write_19}
--    }
--  let {i32 res_adj_21} =
--    loop {i32 acc_adj_23, i32 x_adj_22} = {1i32, x_adj_10}
--    for i_8:i32 < 2i32 do {
--      let {i32 acc_7} = res_acc_11[i_8:+1i32*1i32]
--      let {i32 *^_25} = mul32(loopres_adj_24, acc_7)
--      let {i32 +^_26} = add32(x_adj_22, *^_25)
--      let {i32 *^_27} = mul32(loopres_adj_24, x_5)
--      let {i32 +^_28} = add32(acc_adj_23, *^_27)
--      in {+^_28, +^_26}
--    }
--  in {+^_26}
--}

--  let {i32 res_adj_22} =
--    loop {i32 acc_adj_25, i32 x_adj_24} = {1i32, x_adj_10}
--    for i_23:i32 < 2i32 do {
--      let {i32 acc_7} = res_acc_11[1i32]
--      let {i32 *^_27} = mul32(loopres_adj_26, acc_7)
--      let {i32 +^_28} = add32(x_adj_24, *^_27)
--      let {i32 *^_29} = mul32(loopres_adj_26, x_5)
--      let {i32 +^_30} = add32(acc_adj_25, *^_29)
--      in {+^_30, +^_28}
--    }
--  in {+^_28}
--}

-- Need [acc_7 -> acc_8] due to reassignment
-- Need [loopres_adj_26 -> acc_adj_25]
-- Cannot substitute loopres -> acc because
-- loopres = acc * x, so the substitution will generate a new acc-adj when mkAdjoint is called
-- Substitute loopres -> acc''?

--futhark-ad: let {i32 res_6} =:q

--  loop {i32 acc_26} = {x_5}
--  for i_27:i32 < 3i32 do {
--    let {i32 loopres_28} = mul32(x_5, acc_26)
--    in {loopres_28}
--  }

--Warning at test6.fut:1:42-42:
--  Defaulting ambiguous type to i32.
--futhark-ad: let {i32 bound_41} = add32(3i32, 1i32)
--let {[bound_12]i32 reset_29} = scratch(i32, bound_12)
--let {i32 +^_res_38, i32 +^_res_39} =
--  loop {*[bound_12]i32 acc_adj_30, i32 loopres_adj_40,
--        i32 x_adj_32} = {reset_29, +^_res_38, x_adj_31}
--  for i_27:i32 < bound_41 do {
--    let {i32 idx_42} = sub32(bound_41, i_27)
--    let {i32 acc_26} = update_acc_25[idx_42]
--    let {i32 loopres_adj_33} = 0i32
--    let {i32 *^_34} = mul32(loopres_adj_33, acc_26)
--    let {i32 *^_35} = mul32(loopres_adj_33, x_5)
--    let {i32 +^_36} = add32(x_adj_32, *^_34)
--    let {i32 +^_37} = add32(acc_adj_30, *^_35)
--    in {reset_29, +^_36, +^_37}
--  }











--Warning at test6.fut:1:42-42:
--  Defaulting ambiguous type to i32.
--futhark-ad: let {i32 bound_12} = add32(3i32, 1i32)
--let {[bound_12]i32 empty_acc_13} = scratch(i32, bound_12)
--let {i32 res_6, [bound_12]i32 res_acc_10} =
--  loop {i32 acc_7, *[bound_12]i32 acc_acc_11} = {x_5, empty_acc_13}
--  for i_8:i32 < bound_12 do {
--    let {bool less_than_zero_14} = slt32(i_8, 0i32)
--    let {bool greater_than_size_15} = sle32(bound_12, i_8)
--    let {bool outside_bounds_dim_16} =
--      logor(less_than_zero_14, greater_than_size_15)
--    let {bool outside_bounds_17} = logor(outside_bounds_dim_16, false)
--    let {[bound_12]i32 update_acc_19} =
--      -- Branch returns: {[bound_12]i32}
--      if outside_bounds_17
--      then {acc_acc_11} else {
--        let {[bound_12]i32 write_out_inside_bounds_18} =
--          acc_acc_11 with [i_8] <- acc_7
--        in {write_out_inside_bounds_18}
--      }
--    let {i32 loopres_9} = mul32(x_5, acc_7)
--    in {loopres_9, update_acc_19}
--  }
--let {bool less_than_zero_20} = slt32(3i32, 0i32)
--let {bool greater_than_size_21} = sle32(bound_12, 3i32)
--let {bool outside_bounds_dim_22} =
--  logor(less_than_zero_20, greater_than_size_21)
--let {bool outside_bounds_23} = logor(outside_bounds_dim_22, false)
--let {[bound_12]i32 update_acc_25} =
--  -- Branch returns: {[bound_12]i32}
--  if outside_bounds_23
--  then {res_acc_10} else {
--    let {[bound_12]i32 write_out_inside_bounds_24} =
--      res_acc_10 with [3i32] <- res_6
--    in {write_out_inside_bounds_24}
--  }
--let {i32 bound_42} = add32(3i32, 1i32)
--let {[bound_12]i32 reset_29} = scratch(i32, bound_12)
--let {i32 acc_adj_res_38, i32 +^_res_39, i32 +^_res_40} =
--  loop {*[bound_12]i32 acc_adj_30, i32 loopres_adj_41,
--        i32 x_adj_32} = {reset_29, acc_adj_res_38, x_adj_31}
--  for i_27:i32 < bound_42 do {
--    let {i32 idx_43} = sub32(bound_42, i_27)
--    let {i32 acc_26} = update_acc_25[idx_43]
--    let {i32 loopres_adj_33} = 0i32
--    let {i32 *^_34} = mul32(loopres_adj_33, acc_26)
--    let {i32 *^_35} = mul32(loopres_adj_33, x_5)
--    let {i32 +^_36} = add32(x_adj_32, *^_34)
--    let {i32 +^_37} = add32(acc_adj_30, *^_35)
--    in {reset_29, +^_36, +^_37}
--  }
--in {+^_36}


--futhark-ad: let {i32 bound_12} = add32(3i32, 1i32)
--let {[bound_12]i32 empty_acc_13} = scratch(i32, bound_12)
--let {i32 res_6, [bound_12]i32 res_acc_10} =
--  loop {i32 acc_7, *[bound_12]i32 acc_acc_11} = {x_5, empty_acc_13}
--  for i_8:i32 < bound_12 do {
--    let {bool less_than_zero_14} = slt32(i_8, 0i32)
--    let {bool greater_than_size_15} = sle32(bound_12, i_8)
--    let {bool outside_bounds_dim_16} =
--      logor(less_than_zero_14, greater_than_size_15)
--    let {bool outside_bounds_17} = logor(outside_bounds_dim_16, false)
--    let {[bound_12]i32 update_acc_19} =
--      -- Branch returns: {[bound_12]i32}
--      if outside_bounds_17
--      then {acc_acc_11} else {
--        let {[bound_12]i32 write_out_inside_bounds_18} =
--          acc_acc_11 with [i_8] <- acc_7
--        in {write_out_inside_bounds_18}
--   
--    let {i32 loopres_9} = mul32(x_5, acc_7)
--    in {loopres_9, update_acc_19}
--  }
--let {bool less_than_zero_20} = slt32(3i32, 0i32)
--let {bool greater_than_size_21} = sle32(bound_12, 3i32)
--let {bool outside_bounds_dim_22} =
--  logor(less_than_zero_20, greater_than_size_21)
--let {bool outside_bounds_23} = logor(outside_bounds_dim_22, false)
--let {[bound_12]i32 update_acc_25} =
--  -- Branch returns: {[bound_12]i32}
--  if outside_bounds_23
--  then {res_acc_10} else {
--    let {[bound_12]i32 write_out_inside_bounds_24} =
--      res_acc_10 with [3i32] <- res_6
--    in {write_out_inside_bounds_24}
--  }
--let {i32 bound_42} = add32(3i32, 1i32)
--let {[bound_12]i32 reset_29} = scratch(i32, bound_12)
--let {i32 acc_adj_res_39, i32 +^_res_40, i32 +^_res_38} =
--  loop {*[bound_12]i32 acc_adj_30, i32 loopres_adj_41,
--        i32 x_adj_32} = {reset_29, acc_adj_res_39, x_adj_31}
--  for i_27:i32 < bound_42 do {
--    let {i32 idx_43} = sub32(bound_42, i_27)
--    let {i32 acc_26} = update_acc_25[idx_43]
--    let {i32 loopres_adj_33} = 0i32
--    let {i32 *^_34} = mul32(loopres_adj_33, acc_26)
--    let {i32 *^_35} = mul32(loopres_adj_33, x_5)
--    let {i32 +^_36} = add32(x_adj_32, *^_34)
--    let {i32 +^_37} = add32(acc_adj_30, *^_35)
--    in {reset_29, +^_37, +^_36}
--  }
--in {+^_tes_38}
