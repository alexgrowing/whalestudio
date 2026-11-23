import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MvZOneEqMapUnivSubst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvalAtJetMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowHoweAvg

section Abstract

open GlobalTheory.KJInf Formalism.L2.Ker

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem integrable_term {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (P : FP ι a b)
    (ℓ : FP ι a b →ₗ[ℂ] ℂ) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => ℓ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) * evalAt (fun τ => r k τ * y τ) F) ν := by
  have key : ∀ k, ℓ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) =
      ∑ m ∈ (GlobalTheory.KJAvg.univSubst P).support,
        eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) (coeff m (GlobalTheory.KJAvg.univSubst P)) * ℓ (monomial m 1) := by
    intro k
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff ℓ _ _ (MvPolynomial.support_map_subset _ _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_map]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  simp_rw [key, Finset.sum_mul]
  refine integrable_finset_sum _ fun m _ => ?_
  have hm := (GlobalTheory.KJAvg.integrable_avg_term ν hr (coeff m (GlobalTheory.KJAvg.univSubst P)) y F).mul_const (ℓ (monomial m 1))
  refine hm.congr (Filter.Eventually.of_forall fun k => ?_)
  simp only
  ring

private theorem lft_frDet' (g : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    lft g (frDet ℂ a τ : PY ι a) = C (g τ).det * (frDet ℂ a τ : PY ι a) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_invertible
  intro y _
  have e1 : evalAt y (lft g (frDet ℂ a τ : PY ι a)) = (g τ).det * (y τ).det := by
    rw [evalAt_lft_eq, evalAt_frDet, Matrix.det_mul]
  have e2 : evalAt y (C (g τ).det * (frDet ℂ a τ : PY ι a)) = (g τ).det * (y τ).det := by
    unfold evalAt
    rw [map_mul, eval_C]
    congr 1
    exact evalAt_frDet y τ
  unfold evalAt at e1 e2 ⊢
  rw [map_sub, e1, e2, sub_self]

private theorem lft_prod_frDet_pow (g : ι → Matrix (Fin a) (Fin a) ℂ) (n : ι → ℕ) :
    lft g (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) = C (∏ τ, (g τ).det ^ n τ) * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) := by
  simp only [map_prod, map_pow, lft_frDet', mul_pow, Finset.prod_mul_distrib]

private theorem lft_mem_VV {K : Type} [Group K] [TopologicalSpace K] {r : K → ι → Matrix (Fin a) (Fin a) ℂ}
    (hr : OntoUni r) (lam : ι → DomWeight a) (k : K) (v : VV ℂ lam) : lft (r k) v.1 ∈ VV ℂ lam := by
  have hu : ∀ τ, IsUnit (r k τ).det := fun τ =>
    Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp (hr.uni k τ))
  have h : (rhoK lam (invTrK (fun τ => Matrix.nonsingInvUnit (r k τ) (hu τ))⁻¹) v).1 =
      detTwK lam (invTrK (fun τ => Matrix.nonsingInvUnit (r k τ) (hu τ))⁻¹) • lft (r k) v.1 := rfl
  have hc : detTwK lam (invTrK (fun τ => Matrix.nonsingInvUnit (r k τ) (hu τ))⁻¹) ≠ 0 := by
    unfold detTwK Formalism.BasicNotions.detPow
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => Units.ne_zero _
  have e : lft (r k) v.1 = (detTwK lam (invTrK (fun τ => Matrix.nonsingInvUnit (r k τ) (hu τ))⁻¹))⁻¹ •
      (rhoK lam (invTrK (fun τ => Matrix.nonsingInvUnit (r k τ) (hu τ))⁻¹) v).1 := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.coe_mem _)

private theorem evalAt_smul' (y : ι → Matrix (Fin b) (Fin b) ℂ) (c : ℂ) (p : PY ι b) :
    evalAt y (c • p) = c * evalAt y p := by
  unfold evalAt
  rw [MvPolynomial.smul_eval]

theorem avg_eq_jet (hab : a ≤ b) (ha : 0 < a) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
    (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (P : FP ι a b) (Λ : Module.Dual ℂ (VV ℂ lam)) :
    ∃ Λ' : Module.Dual ℂ (VV ℂ lam'), ∀ (ℓ : FP ι a b →ₗ[ℂ] ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (v : VV ℂ lam)
      (C : ℂ) (c d : K → ℂ), (∀ k, d k * c k = C * ∏ τ, (r k τ).det ^ n τ) →
      ∀ w : K → VV ℂ lam, (∀ k, (w k).1 = c k • lft (r k) v.1) →
      ∀ u : VV ℂ lam', u.1 = C • lft h (jetMap (fun m => ℓ (monomial m 1)) n v.1) →
        ∫ k, d k * ℓ (mvZ (fun τ => (r k τ)⁻¹) h P) * Λ (w k) ∂ν = Λ' u := by
  classical
  have hD0 : (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ =>
      pow_ne_zero _ (Finset.prod_ne_zero_iff.mp (frDet_prod_ne_zero (ι := ι) (a := a)) τ (Finset.mem_univ _))
  obtain ⟨Λe, hΛe⟩ := LinearMap.exists_extend (K := ℂ) (p := VV ℂ lam) Λ
  have hinj : LinearMap.ker (LinearMap.mulRight ℂ (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact mul_right_cancel₀ hD0 hxy
  obtain ⟨g0, hg0⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hT : ∀ x : PY ι a, (Λe.comp g0) (x * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ)) = Λe x := by
    intro x
    have hx := congrArg (fun f => Λe (f x)) hg0
    simpa using hx
  obtain ⟨m, y, Pc, -, hTy⟩ := exists_evalAt_span ι a lam n ℂ (Λe.comp g0)
  choose M Y' S _ hS using fun j => GlobalTheory.KJAvg.avg_span ι a b hab ha lam n K ν r hr (y j) P
  refine ⟨∑ j, ∑ i, (Pc j * S j i) • ((evalLin (Y' j i)).comp (VV ℂ lam').subtype), ?_⟩
  intro ℓ h v C0 c d hd w hw u hu
  have hFV : v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) ∈ Vn lam n := by
    unfold Vn
    exact Submodule.mem_map.mpr ⟨v.1, by rw [GlobalTheory.KJInf.ClsVal.cSpan_eq_VV']; exact v.2, rfl⟩
  have hlftF : ∀ k, lft (r k) (v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ)) = (C (∏ τ, (r k τ).det ^ n τ) * lft (r k) v.1) * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ) := by
    intro k
    rw [map_mul, lft_prod_frDet_pow]
    ring
  have hFk : ∀ k, lft (r k) (v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ)) ∈ Vn lam n := by
    intro k
    rw [hlftF]
    unfold Vn
    refine Submodule.mem_map.mpr ⟨_, ?_, rfl⟩
    rw [GlobalTheory.KJInf.ClsVal.cSpan_eq_VV', C_mul']
    exact Submodule.smul_mem _ _ (lft_mem_VV hr lam k v)
  have hΛw : ∀ k, Λ (w k) = c k * Λe (lft (r k) v.1) := by
    intro k
    rw [← hΛe, LinearMap.comp_apply, Submodule.subtype_apply, hw k, map_smul, smul_eq_mul]
  have hmain : ∀ k, d k * ℓ (mvZ (fun τ => (r k τ)⁻¹) h P) * Λ (w k) =
      C0 * ∑ j, Pc j * ((ℓ.comp (mvZ (fun _ => 1) h).toLinearMap) (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) *
        evalAt (fun τ => r k τ * y j τ) (v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ))) := by
    intro k
    have e1 : mvZ (fun τ => (r k τ)⁻¹) h P = mvZ (fun _ => 1) h (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) := by
      rw [← AlgHom.comp_apply, mvZ_mvZ_comp]
      simp only [mul_one]
    have e2 : Λe (lft (r k) v.1) * ∏ τ, (r k τ).det ^ n τ =
        ∑ j, evalAt (y j) (lft (r k) (v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ))) • Pc j := by
      rw [← hTy _ (hFk k), hlftF, hT, C_mul', map_smul, smul_eq_mul, mul_comm]
    rw [hΛw, e1]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    have e3 : ∀ L0 : ℂ, d k * L0 * (c k * Λe (lft (r k) v.1)) =
        C0 * L0 * (Λe (lft (r k) v.1) * ∏ τ, (r k τ).det ^ n τ) := by
      intro L0
      linear_combination (L0 * Λe (lft (r k) v.1)) * hd k
    rw [e3, e2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, evalAt_lft_eq]
    ring
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)), Integrable (fun k => Pc j *
      ((ℓ.comp (mvZ (fun _ => 1) h).toLinearMap) (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) P) *
        evalAt (fun τ => r k τ * y j τ) (v.1 * (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ)))) ν :=
    fun j _ => (integrable_term ν hr P _ (y j) _).const_mul (Pc j)
  rw [integral_congr_ae (Filter.Eventually.of_forall hmain), integral_const_mul, integral_finset_sum _ hint]
  simp only [integral_const_mul, hS _ _ hFV]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, evalLin_apply, smul_eq_mul, hu, evalAt_smul', evalAt_lft_eq,
    GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, AlgHom.toLinearMap_apply, mvZ_subY]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem substF_rename (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b) :
    GlobalTheory.CompactHowe.substF (fun τ => (g τ).transpose) h (rename (fun k : ι × Fin b × Fin a => (k.1, k.2.2, k.2.1)) P) =
      rename (fun k : ι × Fin b × Fin a => (k.1, k.2.2, k.2.1)) (mvZ g h P) := by
  unfold GlobalTheory.CompactHowe.substF mvZ
  rw [MvPolynomial.aeval_rename, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun f => aeval f P) ?_
  funext v
  simp only [Function.comp_apply, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (C (g _ _ _))]

theorem rhoK_invTr_inv (lam : ι → DomWeight a) (x : ι → GL (Fin a) ℂ) (v : VV ℂ lam) :
    (rhoK lam (invTrK x⁻¹) v).1 =
      (∏ τ, (x τ : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) • lft (fun τ => (x τ : Matrix (Fin a) (Fin a) ℂ)) v.1 := by
  have hT : ∀ τ, (((invTrK x⁻¹) τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = (x τ : Matrix (Fin a) (Fin a) ℂ).transpose :=
    fun τ => rfl
  change detTwK lam (invTrK x⁻¹) • (trAct (invTrK x⁻¹)) v.1 = _
  congr 1
  · unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hT, Matrix.det_transpose]

theorem jetOp_coe {lam : ι → DomWeight a} {lam' : ι → DomWeight b} {n : ι → ℕ} (hJ : JetInVV ℂ lam lam' n)
    (J : (DVar ι a b →₀ ℕ) → ℂ) (v : VV ℂ lam) : (jetOp lam lam' J n v).1 = jetMap J n v.1 := by
  have hm : jetMap J n v.1 ∈ VV ℂ lam' := hJ J v.1 v.2
  simp only [jetOp, retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [Submodule.projectionOnto_apply_of_mem_left _ hm]

end Abstract

section Numbers

open Finset GlobalTheory.SignedHC

theorem step_vals {a b t : ℕ} (hb : b = a + t) {E F : Finset ℚ} (δ c : ℚ) (hE : E.card = a)
    (hFe : F = E.image (· + δ) ∪ TPar.block c t) (hlt : ∀ x ∈ E, ∀ y ∈ TPar.block c t, y < x + δ) (hF : F.card = b)
    (lam : DomWeight a) (lam' : DomWeight b) (h1 : ∀ r, (lam.w r : ℚ) = highestWeight E hE r)
    (h2 : ∀ r, (lam'.w r : ℚ) = highestWeight F hF r) :
    (∀ r : Fin a, (lam'.w (Fin.castLE (by omega) r) : ℚ) = lam.w r + δ - (t : ℚ) / 2) ∧
      ∀ r : Fin b, a ≤ r.1 → (lam'.w r : ℚ) = c + (a : ℚ) / 2 := by
  have hE' : (E.image (· + δ)).card = a := by
    rw [Finset.card_image_of_injective _ (add_left_injective δ)]
    exact hE
  have hlt' : ∀ x ∈ E.image (· + δ), ∀ y ∈ TPar.block c t, y < x := by
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hx
    exact hlt x0 hx0 y hy
  obtain ⟨hA, hB⟩ := highestWeight_below hb c hE' hFe hlt' hF
  constructor
  · intro r
    rw [h2, hA, highestWeight_add δ hE hE' r, h1]
  · intro r hr
    rw [h2, hB r hr]

private theorem wt_grid_eq_highestWeight {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau) {j : ℕ} (hj : j ≤ D.R.m)
    (hc : (entries (parV D sc.cGap j D.R.m τ)).card = (G.V (.grid j D.R.m)).rank)
    (hc' : ((entries (parV D sc.cGap j D.R.m τ)).image Neg.neg).card = (G.V (.grid j D.R.m)).rank)
    (r : Fin (G.V (.grid j D.R.m)).rank) :
    ((wt G (.grid j D.R.m) τ).w r : ℚ) = highestWeight ((entries (parV D sc.cGap j D.R.m τ)).image Neg.neg) hc' r := by
  have hin : InCoset ((((G.V (.grid j D.R.m)).rank : ℚ) - 1) / 2) (entries (parV D sc.cGap j D.R.m τ)) :=
    (isHC_grid D sc.cGap τ hj (rank_grid G hj)).2.2
  rw [highestWeight_neg hc hc' r]
  show (((-(listedWt G (.grid j D.R.m) τ).w r.rev : ℤ)) : ℚ) = _
  unfold listedWt
  push_cast
  exact congrArg Neg.neg (wtOf_cast hc hin r.rev)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem grid_vals {i : ℕ} (hi : i + 1 ≤ D.R.m) (τ : D.what₂.Tau)
    (hle : (G.V (.grid i D.R.m)).rank ≤ (G.V (.grid (i + 1) D.R.m)).rank) :
    (∀ r, ((wt G (.grid (i + 1) D.R.m) τ).w (Fin.castLE hle r) : ℚ) = (wt G (.grid i D.R.m) τ).w r +
      ((if Odd (i + D.R.m) then -(1 / 2) else 0) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) - (sLen D : ℚ) / 2) ∧
    ∀ r : Fin (G.V (.grid (i + 1) D.R.m)).rank, (G.V (.grid i D.R.m)).rank ≤ r.1 →
      ((wt G (.grid (i + 1) D.R.m) τ).w r : ℚ) = (-(cen D sc.cGap τ (D.R.m - i) : ℚ) -
        (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) + ((G.V (.grid i D.R.m)).rank : ℚ) / 2 := by
  have hi0 : i ≤ D.R.m := by omega
  have hrb : (G.V (.grid (i + 1) D.R.m)).rank = (G.V (.grid i D.R.m)).rank + sLen D := by
    rw [rank_grid G hi, rank_grid G hi0]
    simp only [rankV]
    ring
  have cardP : ∀ j, j ≤ D.R.m → (entries (parV D sc.cGap j D.R.m τ)).card = (G.V (.grid j D.R.m)).rank := by
    intro j hj
    unfold parV
    rw [entries_shift, Finset.card_image_of_injective _ (add_left_injective _)]
    exact (card_entries_parD D sc.cGap τ hj).trans (rank_grid G hj).symm
  have cardN : ∀ j, j ≤ D.R.m →
      ((entries (parV D sc.cGap j D.R.m τ)).image Neg.neg).card = (G.V (.grid j D.R.m)).rank := by
    intro j hj
    rw [Finset.card_image_of_injective _ neg_injective, cardP j hj]
  have hFe : (entries (parV D sc.cGap (i + 1) D.R.m τ)).image Neg.neg =
      ((entries (parV D sc.cGap i D.R.m τ)).image Neg.neg).image (· + ((if Odd (i + D.R.m) then -(1 / 2) else 0) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0))) ∪
        TPar.block (-(cen D sc.cGap τ (D.R.m - i) : ℚ) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) (sLen D) := by
    unfold parV
    rw [entries_shift, entries_shift, entries_parD_succ D sc.cGap τ hi]
    exact neg_step _ _ _ _ _
  have hlt : ∀ x ∈ (entries (parV D sc.cGap i D.R.m τ)).image Neg.neg,
      ∀ y ∈ TPar.block (-(cen D sc.cGap τ (D.R.m - i) : ℚ) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) (sLen D), y < x + ((if Odd (i + D.R.m) then -(1 / 2) else 0) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) := by
    intro x hx y hy
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hx
    unfold parV at hx1
    rw [entries_shift] at hx1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
    have hy' : -(-y - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0) ∈ TPar.block (-(cen D sc.cGap τ (D.R.m - i) : ℚ) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) (sLen D) := by
      convert hy using 1
      ring
    rw [neg_sub_mem_block] at hy'
    have hlt0 := parD_below D sc.cGap τ hi hp hy'
    linarith
  exact step_vals hrb _ _ (cardN i hi0) hFe hlt (cardN (i + 1) hi) (wt G (.grid i D.R.m) τ) (wt G (.grid (i + 1) D.R.m) τ)
    (fun r => wt_grid_eq_highestWeight G τ hi0 (cardP i hi0) (cardN i hi0) r)
    (fun r => wt_grid_eq_highestWeight G τ hi (cardP (i + 1) hi) (cardN (i + 1) hi) r)

theorem att_exp {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := by omega
  have hchi : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ (G.ch.chiH (D.R.m - i)) (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ))
      (G.ch.chi_eq _ h1 h2) ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ h1 h2⟩ τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs with hn
  · have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul hchi (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (GlobalTheory.SquareExps.eta_exp hL τ))
    convert h3 using 1
    ring
  · simpa using hchi

theorem rank_lt {i : ℕ} (hi : i < D.R.m) : 0 < (G.V (.grid i D.R.m)).rank ∧
    (G.V (.grid (i + 1) D.R.m)).rank = (G.V (.grid i D.R.m)).rank + sLen D := by
  refine ⟨?_, ?_⟩
  · rw [rank_grid G hi.le]
    exact rankV_pos D _ _
  · rw [rank_grid G (show i + 1 ≤ D.R.m by omega), rank_grid G hi.le]
    simp only [rankV]
    ring

theorem exps_match {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (τ : D.what₂.Tau) {a b : ℚ}
    (ha : HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ a) (hb : HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ b) {e₁ e₂ : ℤ}
    (he₁ : (e₁ : ℚ) = a + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2)
    (he₂ : (e₂ : ℚ) = -(b + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) :
    e₂ = (wt G (.grid (i + 1) D.R.m) τ).detShift ∧
      e₁ + (wt G (.grid i D.R.m) τ).detShift = nuEnd G (.chi i D.R.m : Pair T) τ := by
  obtain ⟨hra, hrb⟩ := rank_lt G hi
  have hsl : 0 < sLen D := by
    simp only [sLen]
    omega
  have hle : (G.V (.grid i D.R.m)).rank ≤ (G.V (.grid (i + 1) D.R.m)).rank := by omega
  have hlast : (G.V (.grid i D.R.m)).rank ≤ (G.V (.grid (i + 1) D.R.m)).rank - 1 := by omega
  have hpos : 0 < (G.V (.grid (i + 1) D.R.m)).rank := by omega
  obtain ⟨gv1, gv2⟩ := grid_vals G (show i + 1 ≤ D.R.m by omega) τ hle
  have ea : a = (cen D sc.cGap τ (D.R.m - i) : ℚ) -
      (if Odd (G.pS (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0) :=
    GlobalTheory.Mem.HeckeExp.hasInfExp_unique ha (att_exp G hL hi _ τ)
  have eb : b = (cen D sc.cGap τ (D.R.m - i) : ℚ) -
      (if Odd (G.pT (.chi i D.R.m : Pair T)).rank then 1 / 2 else 0) :=
    GlobalTheory.Mem.HeckeExp.hasInfExp_unique hb (att_exp G hL hi _ τ)
  have hS : (G.pS (.chi i D.R.m : Pair T)).rank = (G.V (.grid (i + 1) D.R.m)).rank := rfl
  have hT : (G.pT (.chi i D.R.m : Pair T)).rank = (G.V (.grid i D.R.m)).rank := rfl
  have hsg : sgnP (.chi i D.R.m : Pair T) = -1 := rfl
  rw [hS] at ea he₁
  rw [hT] at eb he₂
  rw [hsg] at he₁ he₂
  have pv : ∀ j, j ≤ D.R.m → ((G.V (.grid j D.R.m)).rank % 2 = 0 ↔ (j + D.R.m) % 2 = 1) := by
    intro j hj
    rw [rank_grid G hj, ← Nat.even_iff, ← Nat.odd_iff]
    exact even_rankV (D := D) j D.R.m
  have pa : Odd (G.V (.grid i D.R.m)).rank ↔ Odd (i + 1 + D.R.m) := by
    rw [Nat.odd_iff, Nat.odd_iff]
    have := pv i hi.le
    omega
  have pb : Odd (G.V (.grid (i + 1) D.R.m)).rank ↔ Odd (i + D.R.m) := by
    rw [Nat.odd_iff, Nat.odd_iff]
    have := pv (i + 1) (by omega)
    omega
  have d1 : ((wt G (.grid (i + 1) D.R.m) τ).detShift : ℚ) =
      ((wt G (.grid (i + 1) D.R.m) τ).w ⟨(G.V (.grid (i + 1) D.R.m)).rank - 1, by omega⟩ : ℚ) := by
    simp only [DomWeight.detShift, dif_pos hpos]
  have d0 : ((wt G (.grid i D.R.m) τ).detShift : ℚ) =
      ((wt G (.grid i D.R.m) τ).w ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩ : ℚ) := by
    simp only [DomWeight.detShift, dif_pos hra]
  have g2 := gv2 ⟨(G.V (.grid (i + 1) D.R.m)).rank - 1, by omega⟩ hlast
  have g1 := gv1 ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩
  have hcast : ((G.V (.grid (i + 1) D.R.m)).rank : ℚ) = (G.V (.grid i D.R.m)).rank + sLen D := by
    rw [hrb]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · have key : (e₂ : ℚ) = ((wt G (.grid (i + 1) D.R.m) τ).detShift : ℚ) := by
      rw [d1, g2, he₂, eb]
      by_cases h : Odd (i + 1 + D.R.m)
      · simp only [h, pa.mpr h, if_true]
        ring
      · simp only [h, mt pa.mp h, if_false]
        ring
    exact_mod_cast key
  · have hnn : 0 ≤ (wt G (.grid (i + 1) D.R.m) τ).w ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩ -
        (wt G (.grid (i + 1) D.R.m) τ).detShift := by
      have hd : (wt G (.grid (i + 1) D.R.m) τ).detShift =
          (wt G (.grid (i + 1) D.R.m) τ).w ⟨(G.V (.grid (i + 1) D.R.m)).rank - 1, by omega⟩ := by
        simp only [DomWeight.detShift, dif_pos hpos]
      rw [hd, sub_nonneg]
      exact (wt G (.grid (i + 1) D.R.m) τ).anti (Fin.mk_le_mk.mpr (by omega))
    unfold nuEnd
    rw [dif_pos (show (G.V (.grid i D.R.m)).rank - 1 < (G.V (.grid (i + 1) D.R.m)).rank by omega)]
    unfold DomWeight.natW
    rw [Int.toNat_of_nonneg hnn]
    have key : (e₁ : ℚ) + ((wt G (.grid i D.R.m) τ).detShift : ℚ) =
        ((wt G (.grid (i + 1) D.R.m) τ).w ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩ : ℚ) -
          ((wt G (.grid (i + 1) D.R.m) τ).detShift : ℚ) := by
      have g1' : ((wt G (.grid (i + 1) D.R.m) τ).w ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩ : ℚ) =
          ((wt G (.grid i D.R.m) τ).w ⟨(G.V (.grid i D.R.m)).rank - 1, by omega⟩ : ℚ) +
            ((if Odd (i + D.R.m) then -(1 / 2) else 0) - (if Odd (i + 1 + D.R.m) then -(1 / 2) else 0)) -
              (sLen D : ℚ) / 2 := g1
      rw [g1', d0, d1, g2, he₁, ea, hcast]
      by_cases h : Odd (i + D.R.m)
      · simp only [h, pb.mpr h, if_true]
        ring
      · simp only [h, mt pb.mp h, if_false]
        ring
    exact_mod_cast key

end Numbers

section Grid

open GlobalTheory.KJInf GlobalTheory.SeeSaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

theorem realIn_coe (θ : InfFam D) (N : Std G U) (X : Node) (g : GA D (G.V X)) (τ : D.what₂.Tau) :
    (realIn θ N.fr X g τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) = inB θ (G.V X) (N.frC X) g τ := by
  have h1 : ((frGL N.fr X τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) = N.frC X τ := rfl
  have h2 : Formalism.L2.Pj.archM (G.V X) (θ τ) g = compAt θ τ (Formalism.L2.Theta.mt (G.V X) g) := rfl
  show Units.val ((frGL N.fr X τ)⁻¹ * GlobalTheory.CoefModel.realGL θ (G.V X) g τ * (frGL N.fr X τ)⁻¹⁻¹) = _
  rw [inv_inv, Units.val_mul, Units.val_mul, GlobalTheory.CoefModel.realGL_coe, Matrix.coe_units_inv, h1, h2]
  rfl

theorem det_inB (θ : InfFam D) (N : Std G U) (X : Node) (g : GA D (G.V X)) (τ : D.what₂.Tau) :
    (inB θ (G.V X) (N.frC X) g τ).det = (compAt θ τ (Formalism.L2.Theta.mt (G.V X) g)).det := by
  have hB : IsUnit (N.frC X τ) := by
    have h1 : ((frGL N.fr X τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) = N.frC X τ := rfl
    rw [← h1]
    exact Units.isUnit _
  exact Matrix.det_conj' hB _

theorem realAct_inv_coe (θ : InfFam D) (N : Std G U) (X : Node) (g : GA D (G.V X)) (v : VV ℂ (wt G X)) :
    (realAct θ N.fr X g⁻¹ v).1 =
      (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (G.V X) g)).det ^ (wt G X τ).detShift) • lft (inB θ (G.V X) (N.frC X) g) v.1 := by
  have e : realAct θ N.fr X g⁻¹ v = rhoK (wt G X) (invTrK (realIn θ N.fr X g)⁻¹) v := by
    simp only [realAct, MonoidHom.comp_apply, map_inv]
  rw [e, rhoK_invTr_inv]
  simp only [realIn_coe, det_inB]

theorem map_conj_of_unitary {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u.map (starRingEnd ℂ) = (u⁻¹).transpose ∧ ((u⁻¹).transpose).map (starRingEnd ℂ) = u := by
  have hu' : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : u⁻¹ = star u := Matrix.inv_eq_left_inv hu'
  rw [hinv]
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.star_apply]
  · ext i j
    simp [Matrix.star_apply]

end Grid

open GlobalTheory.KJInf GlobalTheory.SeeSaw in

theorem real_average_jet : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) →
    ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) →
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))),
      ∀ (ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ) (κ : Measure (GinfC (G.V (.grid i D.R.m)))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
        ∀ (k' : GA D (G.V (.grid (i + 1) D.R.m))), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) →
        ∀ v : VV ℂ (wt G (.grid i D.R.m)),
          ∫ k, realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k' *
              ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k' Q) *
              Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
            Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) k'⁻¹
              (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
                (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) (nuEnd G (.chi i D.R.m : Pair T)) v)) := by
  intro D T L sc G W U S μ0 hL i hi a b ha hb e₁ e₂ he₁ he₂ Q Λ
  classical
  have hi1 : i + 1 ≤ D.R.m := hi
  haveI : LocallyCompactSpace (GA D (G.V (.grid i D.R.m))) := (Formalism.IndefR.Eqv.ga_facts D _).2.2.1
  haveI : LocallyCompactSpace (GinfC (G.V (.grid i D.R.m))) := (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
  have hr : OntoUni fun k : GinfC (G.V (.grid i D.R.m)) => inB W.θ (G.V (.grid i D.R.m)) (S.N.frC (.grid i D.R.m)) k.1 :=
    GlobalTheory.SeeSaw.ontoUni_inB D W.θ _ _ W.θ_is (fun τ => GlobalTheory.RealType.frC_on S.N (by exact ⟨hi.le, rfl⟩) τ)
  have hr' : OntoUni fun k : GinfC (G.V (.grid (i + 1) D.R.m)) => inB W.θ (G.V (.grid (i + 1) D.R.m)) (S.N.frC (.grid (i + 1) D.R.m)) k.1 :=
    GlobalTheory.SeeSaw.ontoUni_inB D W.θ _ _ W.θ_is (fun τ => GlobalTheory.RealType.frC_on S.N (by exact ⟨hi1, rfl⟩) τ)
  obtain ⟨hra, hrb⟩ := rank_lt G hi
  have hab : (G.V (.grid i D.R.m)).rank ≤ (G.V (.grid (i + 1) D.R.m)).rank := by omega
  by_cases hex : ∃ κ0 : Measure (GinfC (G.V (.grid i D.R.m))), κ0.IsHaarMeasure ∧ IsProbabilityMeasure κ0
  swap
  · exact ⟨0, fun ℓ κ hκ hκ' => absurd ⟨κ, hκ, hκ'⟩ hex⟩
  obtain ⟨κ0, hκ0, hκ0'⟩ := hex
  obtain ⟨Λ', hΛ'⟩ := avg_eq_jet hab hra (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
    (nuEnd G (.chi i D.R.m : Pair T)) κ0 hr
    (rename (fun x : D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank => (x.1, x.2.2, x.2.1)) Q) Λ
  refine ⟨Λ', fun ℓ κ hκ hκ' k' hk' v => ?_⟩
  have hκe : κ = κ0 := MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ0
  subst hκe
  have hdet : ∀ (k : GinfC (G.V (.grid i D.R.m))) τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k.1)).det ≠ 0 := by
    intro k τ
    rw [← det_inB W.θ S.N (.grid i D.R.m) k.1 τ]
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp (hr.uni k τ))).ne_zero
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m)) (nuEnd G (.chi i D.R.m : Pair T)) :=
    (wtOK_of_defPair G (.chi i D.R.m) ⟨hi1, rfl⟩).2
  have hex' := fun τ => exps_match G hL hi τ (ha τ) (hb τ) (he₁ τ) (he₂ τ)
  have hQ : Q = rename (fun x : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank => (x.1, x.2.2, x.2.1))
      (rename (fun x : D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank => (x.1, x.2.2, x.2.1)) Q) := by
    rw [MvPolynomial.rename_rename]
    exact (MvPolynomial.rename_id_apply Q).symm
  have hnegS : ∀ (k : GinfC (G.V (.grid i D.R.m))) τ,
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS (.chi i D.R.m : Pair T)) (G.toPair (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k').1) =
        compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k') := by
    intro k τ
    show compAt W.θ τ (Formalism.L2.Theta.mt (negSp (G.V (.grid (i + 1) D.R.m))) (negGA (G.V (.grid (i + 1) D.R.m)) k')) = _
    rw [mt_negGA]
  have hd : ∀ k : GinfC (G.V (.grid i D.R.m)), realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k' *
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k.1)).det ^ (wt G (.grid i D.R.m) τ).detShift) =
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ e₂ τ) *
        ∏ τ, (inB W.θ (G.V (.grid i D.R.m)) (S.N.frC (.grid i D.R.m)) k.1 τ).det ^ (nuEnd G (.chi i D.R.m : Pair T) τ) := by
    intro k
    unfold realChar
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hnegS k τ, det_inB]
    show (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ e₂ τ * (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k.1)).det ^ e₁ τ *
      (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k.1)).det ^ (wt G (.grid i D.R.m) τ).detShift = _
    rw [mul_assoc, ← zpow_add₀ (hdet k τ), (hex' τ).2, zpow_natCast]
  have hu : (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) k'⁻¹
      (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1))
        (nuEnd G (.chi i D.R.m : Pair T)) v)).1 =
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ e₂ τ) •
        lft (fun τ => inB W.θ (G.V (.grid (i + 1) D.R.m)) (S.N.frC (.grid (i + 1) D.R.m)) k' τ)
          (Formalism.L2.Ker.jetMap (fun m => (ℓ.comp (rename (fun x : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank => (x.1, x.2.2, x.2.1))).toLinearMap) (monomial m 1))
            (nuEnd G (.chi i D.R.m : Pair T)) v.1) := by
    have hC : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ (wt G (.grid (i + 1) D.R.m) τ).detShift) =
        ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ e₂ τ :=
      Finset.prod_congr rfl fun τ _ => by rw [(hex' τ).1]
    have hJJ : (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) =
        (fun m => (ℓ.comp (rename (fun x : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank => (x.1, x.2.2, x.2.1))).toLinearMap) (monomial m 1)) := by
      funext m
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial]
      rfl
    rw [realAct_inv_coe, jetOp_coe hJ, hC, hJJ]
  have key := hΛ' (ℓ.comp (rename (fun x : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank => (x.1, x.2.2, x.2.1))).toLinearMap)
    (fun τ => inB W.θ (G.V (.grid (i + 1) D.R.m)) (S.N.frC (.grid (i + 1) D.R.m)) k' τ) v
    (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ e₂ τ)
    (fun k => ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k.1)).det ^ (wt G (.grid i D.R.m) τ).detShift)
    (fun k => realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k') hd
    (fun k => realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v)
    (fun k => realAct_inv_coe W.θ S.N _ k.1 v) _ hu
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hsub : realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k' Q =
      rename (fun x : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank => (x.1, x.2.2, x.2.1)) (mvZ (fun τ => (inB W.θ (G.V (.grid i D.R.m)) (S.N.frC (.grid i D.R.m)) k.1 τ)⁻¹)
        (fun τ => inB W.θ (G.V (.grid (i + 1) D.R.m)) (S.N.frC (.grid (i + 1) D.R.m)) k' τ)
        (rename (fun x : D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank => (x.1, x.2.2, x.2.1)) Q)) := by
    rw [← substF_rename, ← hQ]
    unfold realSubst
    refine congrArg₂ (fun A B => GlobalTheory.CompactHowe.substF A B Q) (funext fun τ => ?_) (funext fun τ => ?_)
    · exact (map_conj_of_unitary (hr.uni k τ)).1
    · rw [hnegS k τ]
      exact (map_conj_of_unitary (hr'.uni ⟨k', hk'⟩ τ)).2
  simp only [hsub, LinearMap.comp_apply, AlgHom.toLinearMap_apply]

end GlobalTheory.RowHoweAvg

end
