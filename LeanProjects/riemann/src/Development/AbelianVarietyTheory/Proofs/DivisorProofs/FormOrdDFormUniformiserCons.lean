import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeGeneratorTopForm
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_uniformiser_cons : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (E : Place c) (t : E.ring)
  (w : Fin n → E.ring), Irreducible t →
  (∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ E.const w P)) →
  (∃ x : Fin (n + 1) → K, TrBasis c x) →
  E.formOrd (dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K)) = 0 := by
  intro k K _ _ _ c n E t w ht hw hx
  obtain ⟨x, hx⟩ := hx
  have e : dForm c (Fin.cons (t : K) (fun i => (w i : K)) : Fin (n + 1) → K) =
      E.toRat (n + 1) (dForm E.const (Fin.cons t w : Fin (n + 1) → E.ring)) := by
    have h := TopForm.formMap_dForm (D := n + 1) (α := E.const) (β := c) E.ring.subtype rfl
      (Fin.cons t w : Fin (n + 1) → E.ring)
    refine Eq.trans ?_ h.symm
    congr 1
    funext i
    cases i using Fin.cases <;> rfl
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t', ht'⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht'
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m := by
    have : n + 1 = m + 1 := by exact_mod_cast h2
    omega
  have hG := isFreeGen_dForm_uniformiser_cons k E.ring E.const n t w E.essFiniteType ht ⟨b⟩ hw
  rw [e]
  exact E.formOrd_toRat hG

end GlobalTheory
