let main (x: i32) = loop e = x for i < 10 do e*x


-- futhark-ad: let {i32 loopres_9} = mul32(x_5, e_7)
