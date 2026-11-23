import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdNormGramRLeProdGramDet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatHermHermUnitAniso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LcvNonnegOfIntegralFull
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFullLatticeOfFg
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem hform_gramMatrix {K : Type} [Field K] [StarRing K] {n j : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K) (x y : Fin j → K) :
    hform (Matrix.of fun a b => star (e a) ⬝ᵥ G *ᵥ e b) x y
      = hform G (∑ i, x i • e i) (∑ i, y i • e i) := by
  have h : ∀ a b, hform G (e a) (e b) = star (e a) ⬝ᵥ G *ᵥ e b := by
    intro a b
    simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
      smul_eq_mul, RingHom.id_apply, Pi.star_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, h,
    RingHom.id_apply]
  rw [hform, Matrix.toLinearMapₛₗ₂'_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_eq_mul, Finset.mul_sum, RingHom.id_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => by ring

theorem lcv_nonneg_of_integral_submodule (K : Type) [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] (K0 : Subfield K) (hK0 : IsCMSub K0) (v0 : InfinitePlace K)
    (hv0 : IsConjAt v0) (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hGX : IsRatHerm K0 G X)
    (N : Submodule (𝓞 K) (Fin n → K)) (hN : N.FG)
    (hint : Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform G) N) : 0 ≤ lcv X N := by
  obtain ⟨j, e, Y, L, he, hY, hL, hmem, hgram, hlcv⟩ :=
    GlobalTheory.SpanLattice.exists_fullLattice_of_fg K n X (fun v => (hGX.2 v).1) N hN
  rw [← hlcv]
  refine GlobalTheory.lcv_nonneg_of_integral_full K j (Matrix.of fun a b => star (e a) ⬝ᵥ G *ᵥ e b) Y L hY hL ?_ ?_ ?_
  · exact (GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n j G X hGX).2.2 e he
  · intro x hx y hy
    rw [hform_gramMatrix]
    exact hint _ ((hmem x).1 hx) _ ((hmem y).1 hy)
  · simp only [hgram]
    exact GlobalTheory.prod_norm_gramR_le_prod_gram_det K K0 hK0 n j G X hGX e

end GlobalTheory
