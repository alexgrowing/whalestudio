import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem exists_qz_ne_zero_annihilators_of_ne_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (m : M) (hm : m ≠ 0) : ∃ x : QZ l, x ≠ 0 ∧ ∀ a : ℤ_[l], a • m = 0 → a • x = 0 := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hdec : ∀ (N : Type) [AddCommGroup N] [Module ℤ_[l] N] (a : ℤ_[l]) (ha : a ≠ 0) (y : N),
      a • y = 0 ↔ (l : ℤ_[l]) ^ a.valuation • y = 0 := by
    intro N _ _ a ha y
    conv_lhs => rw [PadicInt.unitCoeff_spec ha, mul_smul]
    exact (PadicInt.unitCoeff ha).isUnit.smul_eq_zero
  by_cases hex : ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0
  · classical
    set r := Nat.find hex with hrdef
    have hr : (l : ℤ_[l]) ^ r • m = 0 := Nat.find_spec hex
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_smul] at hr
      exact hm hr
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l r
    haveI : Fact (1 < l ^ r) := ⟨Nat.one_lt_pow hr0 hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    have hx : (l : ℤ_[l]) ^ r • ι 1 = 0 := by
      have := (hrange (ι 1)).mp ⟨1, rfl⟩
      exact_mod_cast this
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · rw [hdec _ a a0] at ha ⊢
      have hle : r ≤ a.valuation := Nat.find_min' hex ha
      rw [← Nat.add_sub_cancel' hle, pow_add, mul_comm, mul_smul, hx, smul_zero]
  · push_neg at hex
    obtain ⟨ι, hinj, hrange, hlin⟩ := zmodToQZ l 1
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl1⟩
    have hι0 : ι 0 = 0 := by simpa using hlin 0 0
    refine ⟨ι 1, fun h => one_ne_zero (hinj (h.trans hι0.symm)), ?_⟩
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, zero_smul]
    · exact absurd ((hdec _ a a0 m).mp ha) (hex _)

theorem UpperTheory.V.Tower.qzSep :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (m : M), m ≠ 0 → ∃ f : M →ₗ[ℤ_[l]] QZ l, f m ≠ 0 := by
  intro l _ M _ _ m hm
  obtain ⟨x, hx0, hx⟩ := exists_qz_ne_zero_annihilators_of_ne_zero l M m hm
  set K := LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] M m) with hK
  have hle : K ≤ LinearMap.ker (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) := by
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha ⊢
    exact hx a ha
  let f := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] M m) le_rfl
  let g := K.liftQ (LinearMap.toSpanSingleton ℤ_[l] (QZ l) x) hle
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot _ _ le_rfl)
  haveI := UpperTheory.V.PropA.qzInj l
  obtain ⟨h, hh⟩ := Module.Injective.out f hf g
  refine ⟨h, ?_⟩
  have h1 := hh (K.mkQ 1)
  simp only [f, g, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
    one_smul] at h1
  rw [h1]
  exact hx0
