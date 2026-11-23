import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverWithLevel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_level_twelve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), Nonempty (X.Level 12) →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro F _ _ _ 𝔠 R₀ _ k s t H
  apply Rule.ext
  funext R _ _ X h δ
  have h2 : IsUnit ((2 : ℕ) : R) :=
    isUnit_of_dvd_unit ⟨((3 : ℕ) : R), by rw [← Nat.cast_mul]⟩ h
  have h12 : IsUnit ((12 : ℕ) : R) := by
    have : ((12 : ℕ) : R) = ((6 : ℕ) : R) * ((2 : ℕ) : R) := by rw [← Nat.cast_mul]
    rw [this]; exact h.mul h2
  obtain ⟨R', _, σ, X', φ, hff, hpull, hlev⟩ := GlobalTheory.RealMult.exists_faithfullyFlat_level F 𝔠 12 (by norm_num) R h12 X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σa : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  have h' : IsUnit ((6 : ℕ) : R') := by
    have := h.map σ
    rwa [map_natCast] at this
  obtain ⟨δ', hδ', -⟩ := hpull.existsUnique_detGen σ δ
  have e1 := s.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e2 := t.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e3 := H R' X' h' hlev δ'
  apply hff.injective
  change σa (s.val R X h δ) = σa (t.val R X h δ)
  rw [← e1, ← e2, e3]

end GlobalTheory.RealMult
