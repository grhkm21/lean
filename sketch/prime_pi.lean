import data.nat.prime_norm_num
import number_theory.prime_counting

namespace nat
open_locale nat

example : prime 3 :=
begin
  norm_num,
end

example : list.filter prime [0,1,2,3,4,5,6,7,8,9,10] = [2,3,5,7] :=
begin
  unfold list.filter,
  norm_num,
end

example : list.filter prime [2,4] = [2,4] :=
begin
  unfold list.filter,
  norm_num,
end

example : list.countp prime [2,3,5,7] = 4 :=
begin
  unfold list.countp,
end

example : π 400 = 25 :=
begin
  rw [prime_counting, prime_counting', count, list.range],
  simp only [list.range_core, list.countp], -- recursively simp
  norm_num,
end

end nat