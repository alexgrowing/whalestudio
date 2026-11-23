import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K} (E : Place c) {n : ℕ}

theorem ord_neg (f : K) : E.ord (-f) = E.ord f := by
  by_cases hf : f = 0
  · simp [hf]
  have h1 : ((-1 : E.ring) : K) = -1 := rfl
  have hu : IsUnit (-1 : E.ring) := isUnit_one.neg
  have h0 : E.ord (-1) = 0 := by rw [← h1]; exact E.ord_eq_zero hu
  rw [neg_eq_neg_one_mul, E.ord_mul (by norm_num) hf, h0, zero_add]

theorem isFormOrd_neg_iff (η : Forms c n) (a : ℤ) : E.IsFormOrd (-η) a ↔ E.IsFormOrd η a := by
  have key : ∀ η : Forms c n, E.IsFormOrd η a → E.IsFormOrd (-η) a := by
    rintro η ⟨ω, hω, f, rfl, hf⟩
    refine ⟨ω, hω, -f, ?_, ?_⟩
    · rw [Units.val_neg, neg_smul]
    · rw [Units.val_neg, E.ord_neg, hf]
  exact ⟨fun h => by simpa using key _ h, key η⟩

theorem formOrd_neg (η : Forms c n) : E.formOrd (-η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [((E.isFormOrd_neg_iff η a).2 ha).formOrd_eq, ha.formOrd_eq]
  · have h' : ¬ ∃ a, E.IsFormOrd (-η) a := fun ⟨a, ha⟩ => h ⟨a, (E.isFormOrd_neg_iff η a).1 ha⟩
    rw [formOrd, formOrd, dif_neg h, dif_neg h']

theorem disc_neg (η : Forms c n) (φ : K →₀ ℚ) : E.disc (-η) φ = E.disc η φ := by
  rw [disc, disc, formOrd_neg]

end GlobalTheory.FieldPair.Place

namespace GlobalTheory.FieldPair

theorem dForm_comp_perm {k K : Type} [Field k] [Field K] (c : k →+* K) {n : ℕ} (x : Fin n → K)
    (σ : Equiv.Perm (Fin n)) : dForm c (x ∘ σ) = Equiv.Perm.sign σ • dForm c x := by
  rw [dForm_eq, dForm_eq]
  exact (exteriorPower.ιMulti K n).map_perm (fun i => dFun c (x i)) σ

theorem disc_dForm_perm_neg {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ)
    (x : Fin n → K) (σ : Equiv.Perm (Fin n)) (E : Place c) (φ : K →₀ ℚ) :
    E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  refine ⟨?_, E.disc_neg _ φ⟩
  rw [dForm_comp_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, E.disc_neg]

end GlobalTheory.FieldPair
