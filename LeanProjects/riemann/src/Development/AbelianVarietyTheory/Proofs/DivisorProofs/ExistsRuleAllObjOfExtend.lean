import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleAllObjOfThreeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEqOnRapoportUnitSix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevObjRuleEqOfExtend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObj

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem exists_rule_allObj_of_extend : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ R₁ : Type) [CommRing R₀]
  [CommRing R₁] [Algebra R₀ R₁], Function.Injective (algebraMap R₀ R₁) → ∀ (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k)
  (r₁ : Rule (trivialObjectCondition 𝔠) R₁ k),
  (∀ (R : Type) [CommRing R] [Algebra R₁ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport) (δ : X.DetGen),
    r₁.val R X trivial δ = (r₀.extend R₁).val R X hX δ) →
  ∃ r : Rule (trivialObjectCondition 𝔠) R₀ k, ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : X.IsRapoport)
    (δ : X.DetGen), r.val R X trivial δ = r₀.val R X hX δ := by
  intro hDP F _ _ _ 𝔠 R₀ R₁ _ _ _ hinj k r₀ r₁ hyp
  obtain ⟨q3, hq3⟩ := GlobalTheory.RealMult.exists_levObj_rule_eq_of_extend hDP F 𝔠 3 le_rfl R₀ R₁ hinj k r₀ r₁ hyp
  obtain ⟨q4, hq4⟩ := GlobalTheory.RealMult.exists_levObj_rule_eq_of_extend hDP F 𝔠 4 (by norm_num) R₀ R₁ hinj k r₀ r₁ hyp
  obtain ⟨r3, -, hr3⟩ := GlobalTheory.RealMult.RuleDescend.exists_rule_unitObj F 𝔠 3 (by norm_num) R₀ k r₀ q3 hq3
  obtain ⟨r4, -, hr4⟩ := GlobalTheory.RealMult.RuleDescend.exists_rule_unitObj F 𝔠 4 (by norm_num) R₀ k r₀ q4 hq4
  have h42 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 2 R X → unitObj 𝔠 4 R X := by
    intro R _ X h
    change IsUnit ((2 : ℕ) : R) at h
    change IsUnit ((4 : ℕ) : R)
    have : ((4 : ℕ) : R) = ((2 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this]; exact h.mul h
  let t := r4.restrict h42
  have h63 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 6 R X → unitObj 𝔠 3 R X := by
    intro R _ X h
    change IsUnit ((6 : ℕ) : R) at h
    change IsUnit ((3 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this] at h; exact isUnit_of_mul_isUnit_left h
  have h62 : ∀ (R : Type) [CommRing R] (X : Obj F 𝔠 (Sp R)), unitObj 𝔠 6 R X → unitObj 𝔠 2 R X := by
    intro R _ X h
    change IsUnit ((6 : ℕ) : R) at h
    change IsUnit ((2 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this] at h; exact isUnit_of_mul_isUnit_right h
  have hov := GlobalTheory.RealMult.Rule.eq_of_eq_on_rapoport_unit_six hDP F 𝔠 R₀ k (r3.restrict h63) (t.restrict h62) (by
    intro R _ _ X h hX δ
    change r3.val R X (h63 R X h) δ = r4.val R X (h42 R X (h62 R X h)) δ
    exact (hr3 R X _ hX δ).trans (hr4 R X _ hX δ).symm)
  refine GlobalTheory.RealMult.exists_rule_allObj_of_three_two F 𝔠 R₀ k r₀ r3 t ?_ (fun R _ _ X h hX δ ↦ hr3 R X h hX δ) (fun R _ _ X h hX δ ↦ hr4 R X _ hX δ)
  intro R _ _ X h₃ h₂ δ
  have h6 : unitObj 𝔠 6 R X := by
    change IsUnit ((6 : ℕ) : R)
    have : ((6 : ℕ) : R) = ((3 : ℕ) : R) * ((2 : ℕ) : R) := by push_cast; norm_num
    rw [this]; exact h₃.mul h₂
  have := congrArg (fun q : Rule (unitObj 𝔠 6) R₀ k ↦ q.val R X h6 δ) hov
  exact this

end GlobalTheory.RealMult
