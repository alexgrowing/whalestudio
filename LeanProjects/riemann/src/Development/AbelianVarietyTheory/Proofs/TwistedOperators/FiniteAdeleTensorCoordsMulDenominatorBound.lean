import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordDenom

theorem finCoord_mul_denom : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  intro D
  set B := Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E) with hB
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (GlobalTheory.HolDict.ShortVec.intRing D.host.F)
    (fun p : Fin (Module.finrank D.host.F D.host.E) × Fin (Module.finrank D.host.F D.host.E) ×
      Fin (Module.finrank D.host.F D.host.E) => B.repr (B p.1 * B p.2.1) p.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  refine ⟨c, hc, fun e₁ e₂ a b ha hb k => ?_⟩
  have ha' : ∀ i, (e₁ : Af D.host.F) * B.repr a i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := ha
  have hb' : ∀ i, (e₂ : Af D.host.F) * B.repr b i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := hb
  change ((c * e₁ * e₂ : ℕ) : Af D.host.F) * B.repr (a * b) k ∈ _
  rw [← B.sum_repr a, ← B.sum_repr b, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e : ((c * e₁ * e₂ : ℕ) : Af D.host.F) * (B.repr a i * B.repr b j * B.repr (B i * B j) k) =
      ((e₁ : Af D.host.F) * B.repr a i) * ((e₂ : Af D.host.F) * B.repr b j) * ((c : Af D.host.F) * B.repr (B i * B j) k) := by
    push_cast; ring
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (ha' i) (hb' j)) (h (i, j, k))

end GlobalTheory.CoordDenom
