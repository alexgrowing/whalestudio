import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementW
import Formalism.GaussJetBounds.ThmAGauss
import Formalism.GaussJetBounds.GaussJetProofs.OneGauss

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

namespace OrbMul

section Pair

variable {K : Type} [Field K] {σ ι : Type}

lemma jetPairPoly_eq_sum (P : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K)
    (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    jetPairPoly P Th = ∑ κ ∈ S, MvPolynomial.coeff κ P *
      MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  unfold jetPairPoly
  refine Finset.sum_subset hS fun κ _ hκ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]

lemma jetPairPoly_add_left (P Q : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K) :
    jetPairPoly (P + Q) Th = jetPairPoly P Th + jetPairPoly Q Th := by
  classical
  rw [jetPairPoly_eq_sum (P + Q) Th (P.support ∪ Q.support) MvPolynomial.support_add,
    jetPairPoly_eq_sum P Th (P.support ∪ Q.support) Finset.subset_union_left,
    jetPairPoly_eq_sum Q Th (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

lemma jetPairPoly_monomial (κ : ι →₀ ℕ) (c : MvPolynomial σ K) (Th : MvPowerSeries ι K) :
    jetPairPoly (MvPolynomial.monomial κ c) Th =
      c * MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  classical
  rw [jetPairPoly_eq_sum _ Th {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

end Pair

section Exps

variable {ι₁ ι₂ : Type}

def jn (a : ι₁ →₀ ℕ) (b : ι₂ →₀ ℕ) : ι₁ ⊕ ι₂ →₀ ℕ :=
  a.mapDomain Sum.inl + b.mapDomain Sum.inr

end Exps

section Along

variable {K : Type} [Field K] {ι₁ ι₂ σ₁ σ₂ : Type} [Finite ι₁] [Finite ι₂]

end Along

section Trunc

variable {K : Type} [Field K] {σ ι : Type} [Finite ι]

end Trunc

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ₁ σ₂ : Type}

lemma norm_coeff_rename_le {σ τ : Type} (e : σ → τ) (he : Function.Injective e)
    (A : MvPolynomial σ K) {B : ℝ} (hA : ∀ n, ‖MvPolynomial.coeff n A‖ ≤ B) (n : τ →₀ ℕ) :
    ‖MvPolynomial.coeff n (MvPolynomial.rename e A)‖ ≤ B := by
  by_cases hn : ∃ u : σ →₀ ℕ, u.mapDomain e = n
  · obtain ⟨u, rfl⟩ := hn
    rw [MvPolynomial.coeff_rename_mapDomain e he]
    exact hA u
  · rw [MvPolynomial.coeff_rename_eq_zero e A n fun u hu => absurd ⟨u, hu⟩ hn, norm_zero]
    exact le_trans (norm_nonneg _) (hA 0)

end Norm

end OrbMul

namespace OrbMul

lemma linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (x : ZV d N0 N1) :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) x = MvPowerSeries.X x := by
  classical
  unfold linSub idM
  simp

lemma thetaZ_eq {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) :
    thetaZ g U ε be = MvPowerSeries.subst g U *
      mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be) := by
  unfold thetaZ
  rw [show (linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) =
      MvPowerSeries.X from funext linSub_idM, MvPowerSeries.subst_self]
  rfl

end OrbMul

end Formalism.DworkPowerSeriesWeights
