import tactic

-- Flatten list of pairs
def flatten_pairs : list (ℕ × ℕ) → list ℕ
  | []             := []
  | ((x, y) :: xs) := [x, y] ++ flatten_pairs xs

-- Idea: First construct a function that takes an array of digits and applies "look and say" to it
-- l is stored in reverse order i.e. most recent one is at the front, in the format [(freq, num)]
-- f_aux [] l = l
-- f_aux [1, 1] [(1, 1)] = [(1, 3)]
-- f_aux [1, 1] [(2, 1)] = [(1, 2), (2, 1)]
def look_and_say_aux : list ℕ → list (ℕ × ℕ) → list (ℕ × ℕ)
  | [] l                 := l
  | (x::xs) []           := look_and_say_aux xs [(1, x)]
  | (x::xs) ((f, n)::ls) := look_and_say_aux xs ((ite (x = n) [(f + 1, n)] [(1, x), (f, n)]) ++ ls)

-- Calls look_and_say_aux
-- [1, 1, 2, 3, 3, 1] -> [(1, 1), (3, 2), (2, 1), (1, 2)] -> 
def look_and_say : ℕ → list ℕ → list ℕ
  | 0 l       := l
  | (n + 1) l := look_and_say n (flatten_pairs $ list.reverse $ look_and_say_aux l list.nil)

set_option profiler true

-- Test case: Applying the operation 5 time (361ms)
example {l : list ℕ} (h : l = look_and_say 5 [1]) : l = [3, 1, 2, 2, 1, 1] :=
begin
  norm_num [look_and_say, look_and_say_aux, flatten_pairs] at h,
  exact h,
end

-- Test case: Applying the operation 15 times (39.9s)
example {l : list ℕ} (h : l = look_and_say 15 [1]) : l = [1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1] :=
begin
  norm_num [look_and_say, look_and_say_aux, flatten_pairs] at h,
  exact h,
end

-- TODO (Idea): Prove correspondence between atoms and sequence is actually valid i.e.
--
--          Decompose
-- Sequence --------> Atom
--    |                 |
--    |                 |   look_and_say
--    v                 v
-- Sequence <-------- Atom
--          Map atoms
-- 
-- Commutes