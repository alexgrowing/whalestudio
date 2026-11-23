import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
open scoped Matrix ComplexOrder

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_conj_bVV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (i : VVIdx lam) :
    MvPolynomial.map ((starRingEnd ℂ).comp φ) (bVV K lam i : VV K lam).1 = MvPolynomial.map φ (bVV K lam i : VV K lam).1 := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [bVV_coe, hQ, MvPolynomial.map_map, MvPolynomial.map_map]
  rw [RingHom.ext_int (((starRingEnd ℂ).comp φ).comp (Int.castRingHom K)) (φ.comp (Int.castRingHom K))]

theorem map_smul_pol {K : Type} [Field K] {σ : Type} (φ : K →+* ℂ) (r : K) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem pairB_conj_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (y : VV K lam) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map φ y.1)) (MvPolynomial.map φ y.1) =
      star (fun i => φ ((bVV K lam).repr y i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map φ *ᵥ (fun i => φ ((bVV K lam).repr y i)) := by
  have hy : y.1 = ∑ i, (bVV K lam).repr y i • (bVV K lam i : VV K lam).1 := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [Submodule.coe_sum]
    rfl
  rw [MvPolynomial.map_map, hy]
  simp only [map_sum, map_smul_pol, map_conj_bVV, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← GlobalTheory.PeriodOnStep.map_pairB, dotProduct, Matrix.mulVec, Matrix.map_apply, GlobalTheory.TestLat.Compare.gramB, Matrix.of_apply, pairBK_apply,
    Pi.star_apply, RingHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem herm_mk {K : Type} [Field K] {ι : Type} [Fintype ι] (M : Matrix ι ι K) (φ : K →+* ℂ) (hM : (M.map φ).PosDef)
    (a : ι → K) :
    star (fun i => (InfinitePlace.mk φ).embedding (a i)) ⬝ᵥ M.map (InfinitePlace.mk φ).embedding *ᵥ
        (fun i => (InfinitePlace.mk φ).embedding (a i)) =
      star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h]
    have hr := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => φ (a i))
    have hc : starRingEnd ℂ (star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i))) =
        star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hr).2.symm
    rw [← hc]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
      map_mul, starRingEnd_apply, star_star]

theorem normAt_sq_eq_cSum {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) =
      cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  have h0 := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH B.wts I.Ch I.sel (I.tup a) I.Ps hX).2 (InfinitePlace.mk B.embLL)
  refine (h0 (x : (MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps).V)).trans ?_
  rw [cSum_apply]
  unfold GSD.ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cTerm
  rw [GSD.wt_eq]
  congr 1
  rw [GlobalTheory.PeriodClassSum.pairAt_eq, GlobalTheory.PeriodClassSum.row_gramV]
  exact (herm_mk _ _ (GlobalTheory.PeriodClassSum.gramB_posDef _ _) _).trans (pairB_conj_map _ _ _).symm

end GlobalTheory.Mem.Df
