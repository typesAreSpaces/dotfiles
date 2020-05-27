cartesian_aux :: [[a]] -> [[a]] -> [[a]]
cartesian_aux aux []     = aux
cartesian_aux aux (x:xs) = cartesian_aux (concat (map (\x1 -> (map (\x2 -> x1 : x2) aux)) x)) xs

cartesian_aux_2 = cartesian_aux [[]]

cartesian_prod = \x -> cartesian_aux_2 (reverse x)
