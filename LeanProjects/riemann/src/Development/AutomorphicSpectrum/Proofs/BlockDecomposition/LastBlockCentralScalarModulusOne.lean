import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ZjScalar

theorem sum_card_mul_modExp {h : ℕ} (d : Fin h → ℕ) :
    ∑ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = 0 := by
  simp only [modExp, Fintype.card_fin, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : b < a
  · simp [hab, mul_comm]
  · simp [hab]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (x : ℝ) (hx : x ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := by
  have : a ≤ j := by
    have := a.2
    exact Fin.le_def.2 (by omega)
  simp [Zl.JC.zj, this]

theorem nabs_det_zj_last {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) (hj : j.val + 1 = h) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) = nabs k t ^ (d a) := by
  rw [zj_last d t j hj a]
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = t ^ (d a) := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

theorem zj_last_scalar_modulus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h)
    (hj : j.val + 1 = h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧
      modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  constructor
  · apply Units.ext
    ext p q
    obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
    obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, zj_last d t j hj a]
      by_cases hxy : x = y
      · subst hxy
        simp [Matrix.GeneralLinearGroup.scalar]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
        simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
    · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
        hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
      rw [leviEmb_apply_ne k _ _ hab]
      simp [Matrix.GeneralLinearGroup.scalar, this]
  · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
    simp only [modulus, nabs_det_zj_last d t j hj]
    have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
        nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
      rw [zpow_mul, zpow_natCast]
    simp only [this]
    rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]

end GlobalTheory.CompanionTheory.ZjScalar
