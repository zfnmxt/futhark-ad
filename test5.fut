let main (x: i32) (m: i32) = loop (n,e) = (1,x) while n < m do (n+1, e*x)


-- let {bool res_15, i32 res_16, i32 res_17} =
--   loop {bool loop_while_18, i32 n_19, i32 e_20} = {loop_cond_14, 1i32, x_12}
--   while loop_while_18 do {
--     let {i32 loopres_21} = add32(1i32, n_19)
--     let {i32 loopres_22} = mul32(x_12, e_20)
--     let {bool loop_cond_23} = slt32(loopres_21, m_13)
--     in {loop_cond_23, loopres_21, loopres_22}
--   }

--entry {i32, i32, i32, i32} main (i32 x_12, i32 m_13, i32 x_grad_24,
--                                 i32 m_grad_25) = {
--  let {bool loop_cond_14} = slt32(1i32, m_13)
--  let {bool loop_cond_grad_26} = slt32(1i32, m_13)
--  let {bool res_15, i32 res_16, i32 res_17, bool res_grad_37, i32 res_grad_38,
--       i32 res_grad_39} =
--    loop {bool loop_while_18, i32 n_19, i32 e_20, bool loop_while_grad_27,
--          i32 n_grad_28, i32 e_grad_29} = {loop_cond_14, 1i32, x_12,
--                                           loop_cond_grad_26, 0i32, x_grad_24}
--    while loop_while_18 do {
--      let {i32 loopres_21} = add32(1i32, n_19)
--      let {i32 x+^y_31} = add32(0i32, n_grad_28)
--      let {i32 loopres_grad_30} = x+^y_31
--      let {i32 loopres_22} = mul32(x_12, e_20)
--      let {i32 x*^y_33} = mul32(x_grad_24, e_20)
--      let {i32 x*^y_34} = mul32(x_12, e_grad_29)
--      let {i32 x+^y_35} = add32(x*^y_33, x*^y_34)
--      let {i32 loopres_grad_32} = x+^y_35
--      let {bool loop_cond_23} = slt32(loopres_21, m_13)
--      let {bool loop_cond_grad_36} = slt32(loopres_21, m_13)
--      in {loop_cond_23, loopres_21, loopres_22, loop_cond_grad_36,
--          loopres_grad_30, loopres_grad_32}
--    }
--  in {res_16, res_17, res_grad_38, res_grad_39}
--}
