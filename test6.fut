let main (x: i32) = loop acc = x for i < 2 do acc*x


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
