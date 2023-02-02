import tactic

-- Idea: First construct a function that takes an array of digits and applies "look and say" to it

-- l is stored in reverse order i.e. most recent one is at the front, in the format [(num, freq)]
-- f_aux [] l = l
-- f_aux [1, 1] [(1, 1)] = [(1, 3)]
-- f_aux [1, 1] [(2, 1)] = [(1, 2), (2, 1)]
def f_aux : list ℕ → list (ℕ × ℕ) → list (ℕ × ℕ)
  | [] l := l
  | (x :: xs) [] := f_aux xs [(x, 1)]
  | (x :: xs) ((l, c) :: ls) := f_aux xs ((ite (x = l) [(l, c + 1)] [(x, 1), (l, c)]) ++ ls)

-- Swap pairs in list of pairs
def swap_pairs : list (ℕ × ℕ) → list (ℕ × ℕ)
  | [] := []
  | ((x, y) :: xs) := (y, x) :: swap_pairs xs

-- Flatten list of pairs
def flatten_pairs : list (ℕ × ℕ) → list ℕ
  | [] := []
  | ((x, y) :: xs) := [x, y] ++ flatten_pairs xs

-- Calls f_aux
-- [1, 1, 2, 3, 3, 1] -> [(1, 1), (3, 2), (2, 1), (1, 2)] -> 
def f (l : list ℕ) : list ℕ := flatten_pairs (list.reverse (swap_pairs (f_aux l list.nil)))

example {l : list ℕ} (h : l = f [1, 1, 2, 3, 3, 1]) : l = [2, 1, 1, 2, 2, 3, 1, 1] :=
begin
  simp [f, flatten_pairs, swap_pairs, f_aux] at h,
  norm_num at h,
  exact h,
end