import group_theory.subgroup.basic

variables {G H : Type*} [group G] [group H]

theorem hom_is_trivial_if_kernel_eq_group
(φ : G →* G) (h : φ.ker = ⊤) : φ = 1 :=
begin
  apply fun_like.ext,
  intro g,
  rw [monoid_hom.one_apply, ← monoid_hom.mem_ker, h],
  trivial,
end