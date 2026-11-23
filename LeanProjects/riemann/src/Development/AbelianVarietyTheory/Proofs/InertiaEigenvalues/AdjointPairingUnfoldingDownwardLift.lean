import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFormulaOfKernel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
open GlobalTheory.Grow
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.AdjUnfold

set_option maxHeartbeats 4000000 in

theorem integral_val_thF_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y u
  have hm := hL.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hL.thP.ωP i t
  have hpt := hL.thP.pt_theta i t
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hJt : ∀ k, IsThetaFunO R.ψ (Vc D i) (Wc D i) (jointVec R i t v (b k)) := fun k => hpt _
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ u)
  have hFc : Continuous (R.extV i t u) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t u (γ * h) = R.extV i t u h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hGk : ∀ k, RapidDec (Vc D i) (fun h => ⟪R.extV i t u h, b k⟫_ℂ) := fun k =>
    RapidDec.of_isCompact (fun γ hγ h => by simp only [hFi γ hγ h]) (hFc.inner continuous_const) hK
      (fun g => by
        obtain ⟨γ, hγ, c', hc', e⟩ := hKc g
        exact ⟨γ⁻¹, inv_mem hγ, by rw [e, inv_mul_cancel_left]; exact hc'⟩)
  obtain ⟨-, hr, -⟩ := hm.HW i (sg0 D A)
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  have hF : RapidDec (Wc D i) (fun g => starRingEnd ℂ (val R i v y g)) :=
    (rapidDec_of_cuspForm hP hθ (hTm.aut fun ρ => v ρ) (hTm.cusp fun ρ => v ρ)).conj
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin n → GA D (Wc D i) → GA D (Vc D i) → ℂ, Φ = fun k g h =>
      thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) * starRingEnd ℂ (val R i v y g) *
        starRingEnd ℂ ⟪R.extV i t u h, b k⟫_ℂ := ⟨_, rfl⟩
  have hint : ∀ k, Integrable (Function.uncurry (Φ k))
      (((R.νW i).restrict (R.fdW i)).prod ((R.νV i t).restrict (R.fdV i t))) := fun k => by
    rw [hΦ]
    exact GlobalTheory.ChainOnto.ThetaSwap.integrable_prod hθ hω (hJt k) hHV hfdV hHW hfdW (hGk k) hF
  have hthF : ∀ g, R.thF i t u (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) ∂(R.νV i t) :=
    fun g => (hL.thP.thF i t).elim fun _ h => (congrFun (h.2 u v) g).trans
      (h.1.eq ((R.extV i t).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g)
  have hexp : ∀ g h, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) =
      ∑ k, ⟪b k, R.extV i t u h⟫_ℂ * thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) := by
    intro g h
    have e : (R.cV i).ext ((R.HV i t).e u) h = ∑ k, ⟪b k, R.extV i t u h⟫_ℂ • b k := (b.sum_repr' _).symm
    rw [e, map_sum]
    unfold jointVec RealDat.ptP
    simp only [map_sum, map_smul, thetaKO, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hL1 : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g =
      ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) := by
    have hae : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), ∀ k,
        Integrable (fun h => Φ k g h) ((R.νV i t).restrict (R.fdV i t)) :=
      ae_all_iff.2 fun k => (hint k).prod_right_ae
    filter_upwards [hae] with g hg
    rw [hthF g, ← integral_const_mul]
    have e : ∀ h, star (val R i v y g) * thetaKO (R.ωP i t) h g
        (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) = ∑ k, Φ k g h := by
      intro h
      rw [hexp g h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ, inner_conj_symm, Complex.star_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact integral_finset_sum _ fun k _ => hg k
  have hR : ∀ h, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ = ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) := by
    intro h
    simp only [upVec, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hΦ, upLift]
    rw [integral_mul_const, ← integral_conj, inner_conj_symm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
  calc ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i)
      = ∫ g in R.fdW i, ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) := integral_congr_ae hL1
    _ = ∑ k, ∫ g in R.fdW i, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) :=
        integral_finset_sum _ fun k _ => (hint k).integral_prod_left
    _ = ∑ k, ∫ h in R.fdV i t, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        Finset.sum_congr rfl fun k _ => integral_integral_swap (hint k)
    _ = ∫ h in R.fdV i t, ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        (integral_finset_sum _ fun k _ => (hint k).integral_prod_right).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => (hR h).symm)

end GlobalTheory.AdjUnfold
