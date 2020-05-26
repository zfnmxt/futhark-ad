let main (x: i32) (m: i32) = loop (n,e) = (1,x) while n < m do (n+1, e*x)


-- let {bool res_15, i32 res_16, i32 res_17} =
--   loop {bool loop_while_18, i32 n_19, i32 e_20} = {loop_cond_14, 1i32, x_12}
--   while loop_while_18 do {
--     let {i32 loopres_21} = add32(1i32, n_19)
--     let {i32 loopres_22} = mul32(x_12, e_20)
--     let {bool loop_cond_23} = slt32(loopres_21, m_13)
--     in {loop_cond_23, loopres_21, loopres_22}
--   }
