import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in

theorem _root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis {k K : Type} [Field k] [CharZero k]
    [Field K] (c : k →+* K) {n : ℕ} {x : Fin n → K} (hx : _root_.GlobalTheory.FieldPair.TrBasis c x) :
    _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) := by
  letI : Algebra k K := c.toAlgebra
  have hb : IsTranscendenceBasis k x := hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    hb.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hbx⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hb.1
  exact _root_.GlobalTheory.TopForm.isFreeGen_dForm x b (fun i => by rw [hbx i])

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in

theorem _root_.GlobalTheory.FieldPair.formOrd_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K]
    (c : k →+* K) (n : ℕ) (x : Fin n → K), _root_.GlobalTheory.FieldPair.TrBasis c x →
  _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) ∧
  ∀ E : _root_.GlobalTheory.FieldPair.Place c,
    (∃ ω : _root_.GlobalTheory.TopForm.Forms E.const n, _root_.GlobalTheory.TopForm.IsFreeGen E.ring ω) ∧
    (∀ η : _root_.GlobalTheory.TopForm.Forms c n, η ≠ 0 → E.IsFormOrd η (E.formOrd η)) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (f : K), η ≠ 0 → f ≠ 0 →
      E.formOrd (f • η) = E.ord f + E.formOrd η) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a →
      E.formOrd η = a) := by
  intro k K _ _ _ c n x hx
  refine ⟨_root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis c hx, fun E => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact E.exists_isFreeGen hx
  · intro η hη
    exact E.isFormOrd_formOrd hx hη
  · intro η f hη hf
    exact E.formOrd_smul hx hη hf
  · intro η a _ h
    exact h.formOrd_eq

end GlobalTheory.FieldPair
