import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open UpperTheory.V.HV

namespace GlobalTheory.Ord2.CoefDual

variable (l : ℕ) [Fact l.Prime] (c : Coef l)

def dualModule : Module c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) where
  smul a f := f ∘ₗ LinearMap.mulLeft ℤ_[l] a
  one_smul f := by ext x; show f (1 * x) = f x; rw [one_mul]
  mul_smul a b f := by ext x; show f (a * b * x) = f (b * (a * x)); rw [mul_comm a b, mul_assoc]
  smul_zero a := by ext x; show (0 : c.O →ₗ[ℤ_[l]] ℤ_[l]) (a * x) = 0; rfl
  smul_add a f g := by ext x; show (f + g) (a * x) = f (a * x) + g (a * x); rfl
  add_smul a b f := by ext x; show f ((a + b) * x) = f (a * x) + f (b * x); rw [add_mul, map_add]
  zero_smul f := by ext x; show f (0 * x) = 0; rw [zero_mul, map_zero]

theorem dualModule_apply (a : c.O) (f : c.O →ₗ[ℤ_[l]] ℤ_[l]) (x : c.O) :
    (letI := dualModule l c; a • f) x = f (a * x) := rfl

theorem dual_tower :
    letI := dualModule l c; IsScalarTower ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine ⟨fun r a f => ?_⟩
  ext x
  rw [dualModule_apply, LinearMap.smul_apply, dualModule_apply, smul_mul_assoc, map_smul]

theorem dual_torsionFree :
    letI := dualModule l c; Module.IsTorsionFree c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[l]) (I := Ideal.span {a}) ha
    (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  ext x
  have h1 : r • f x = 0 := by
    rw [← map_smul, Algebra.smul_def, hb, mul_assoc, ← dualModule_apply, h]
    rfl
  simpa [hr0] using h1

end GlobalTheory.Ord2.CoefDual

open GlobalTheory.Ord2.CoefDual in

theorem GlobalTheory.Ord2.coef_dual_free_rank_one :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ τ : c.O →ₗ[ℤ_[l]] ℤ_[l],
      ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = τ (a * x) := by
  intro l _ c
  letI := dualModule l c
  haveI := dual_tower l c
  haveI : Module.IsTorsionFree ℤ_[l] c.O := FaithfulSMul.to_isTorsionFree ℤ_[l] c.O
  haveI : Module.Free ℤ_[l] c.O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := dual_torsionFree l c
  haveI : Module.Free c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.free_of_finite_type_torsion_free'
  have h1 := Module.finrank_linearMap ℤ_[l] ℤ_[l] c.O ℤ_[l]
  have h2 := Module.finrank_mul_finrank ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l])
  have hpos : 0 < Module.finrank ℤ_[l] c.O := Module.finrank_pos
  have hr : Module.finrank c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) = 1 := by
    rw [h1, Module.finrank_self, mul_one] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (mul_one _).symm)
  let b := Module.finBasisOfFinrankEq c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) hr
  refine ⟨b 0, fun f => ⟨b.repr f 0, fun x => ?_, fun a ha => ?_⟩⟩
  · have hs := b.sum_repr f
    rw [Fin.sum_univ_one] at hs
    rw [← dualModule_apply, hs]
  · have hf : f = a • b 0 := LinearMap.ext fun x => (ha x).trans (dualModule_apply l c a (b 0) x).symm
    rw [hf, map_smul, b.repr_self]
    simp

end
