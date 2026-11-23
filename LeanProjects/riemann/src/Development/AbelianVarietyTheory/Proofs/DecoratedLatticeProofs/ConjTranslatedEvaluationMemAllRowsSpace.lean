import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFiniteStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VanishTranslates
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.SeeHH

theorem inner_antiunitary_swap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (U : E ≃ₗᵢ⋆[ℂ] F) (x y : E) : ⟪U x, U y⟫_ℂ = ⟪y, x⟫_ℂ := by
  have hI : ∀ z : E, U (Complex.I • z) = (-Complex.I) • U z := by
    intro z; rw [map_smulₛₗ]; simp
  have h1 : ‖U x + U y‖ = ‖y + x‖ := by rw [← map_add, U.norm_map, add_comm]
  have h2 : ‖U x - U y‖ = ‖y - x‖ := by rw [← map_sub, U.norm_map, norm_sub_rev]
  have h3 : ‖U x - Complex.I • U y‖ = ‖y - Complex.I • x‖ := by
    have e1 : U x - Complex.I • U y = U (x + Complex.I • y) := by
      rw [map_add, hI, neg_smul, sub_eq_add_neg]
    have e2 : y - Complex.I • x = (-Complex.I) • (x + Complex.I • y) := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  have h4 : ‖U x + Complex.I • U y‖ = ‖y + Complex.I • x‖ := by
    have e1 : U x + Complex.I • U y = U (x - Complex.I • y) := by
      rw [map_sub, hI, neg_smul, sub_neg_eq_add]
    have e2 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]; abel
    rw [e1, U.norm_map, e2, norm_smul]; simp
  rw [inner_eq_sum_norm_sq_div_four (U x) (U y), inner_eq_sum_norm_sq_div_four y x]
  simp only [RCLike.I_to_complex]
  rw [h1, h2, h3, h4]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem star_toLp_eq {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hm : MemLp f 2 (muX X))
    (hs : MemLp (fun x => star (f x)) 2 (muX X)) :
    star (hm.toLp f) = hs.toLp (fun x => star (f x)) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hs.coeFn_toLp] with x a1 a2 a3
  rw [a1, a3, Pi.star_apply, a2]

theorem re_fix_of_row {D : D7} (X : HidaSetting D) {f : X.B.I.GA → ℂ} (hf : RowFun X f) (hm : MemLp f 2 (muX X)) :
    X.B.Re (star (hm.toLp f)) = star (hm.toLp f) := by
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
  rw [star_toLp_eq X hm hs]
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
  have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
  refine Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) ?_ ?_ hs ?_
  · exact (continuous_star.comp hf.cont).measurable
  · intro γ hγ y
    rw [hf.left γ hγ y]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfun : (fun g => X.B.e g * star (f (y * (1, g)))) =
        X.K2.indicator (fun _ => star (f y) / ((X.B.μf X.K2).toReal : ℂ)) := by
      funext g
      rw [X.e_eq g]
      by_cases hg : g ∈ X.K2
      · have hg' : g ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_pos hg', Set.indicator_of_mem hg, hf.right g hg y]
        have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
        have hc : star (X.chi2 g) * X.chi2 g = 1 := by
          rw [← starRingEnd_apply, Complex.conj_mul', hn]; simp
        have e2 : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd g = X.chi2 g := rfl
        have ev : X.B.μf (K2set X.B.I X.B.g X.e0 X.z0 X.bw) = X.B.μf X.K2 := rfl
        rw [e2, ev, star_mul', star_star, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (star (f y) * (((X.B.μf X.K2).toReal : ℂ))⁻¹) * hc
      · have hg' : g ∉ K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
        rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
    rw [hfun, integral_indicator hKM, setIntegral_const]
    simp only [Measure.real]
    rw [Complex.real_smul]
    have hvc : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
    rw [mul_comm, div_mul_cancel₀ _ hvc]

end GlobalTheory.Core.Mi.SeeHH

namespace GlobalTheory.Core.Mi.SeeHH

theorem real_shift {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (t : GA D (D.sp.Y 0)) (ht : t ∈ GfC (D.sp.Y 0)) (hR : RealSplit X h θ) (v₀ : M.Vec) (g : X.B.I.Ginf) :
    ∃ a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ,
      (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ)) ∧
      (∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ)) ∧
      ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) ∧
        ∀ U ∈ Mult θ M J χ, ∀ x, U v₀ ((iotaX X h).symm (x * (g, 1)) * t) = U w ((iotaX X h).symm x * t) := by
  classical
  choose a ha hb using fun τ => hR.2.2.2 τ (g (X.pl.symm τ))
  have hsm : ∀ τ, M.rep τ (a τ) (v₀ τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D (D.sp.Y 0) S M τ (a τ) (ha τ) _ (v₀ τ).2
  let gs : Finset D.what₂.Tau → X.B.I.GA := fun s => ((fun v => if X.pl v ∈ s then g v else 1), 1)
  let ws : Finset D.what₂.Tau → M.Vec := fun s τ => if τ ∈ s then ⟨_, hsm τ⟩ else v₀ τ
  have key : ∀ s : Finset D.what₂.Tau, ∀ U ∈ Mult θ M J χ, ∀ x,
      U v₀ ((iotaX X h).symm (x * gs s) * t) = U (ws s) ((iotaX X h).symm x * t) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro U _ x
      have e1 : gs ∅ = 1 := Prod.ext (funext fun v => by simp [gs]) rfl
      have e2 : ws ∅ = v₀ := funext fun τ => by simp [ws]
      rw [e1, e2, mul_one]
    | insert τ s hτ ih =>
      intro U hU x
      obtain ⟨he2, hoth, -⟩ := hR.2.2.1 τ (a τ) (ha τ)
      have hws : ws s τ = v₀ τ := by simp [ws, hτ]
      have hupd : ws (insert τ s) = Function.update (ws s) τ ⟨_, hsm τ⟩ := by
        funext σ
        by_cases hσ : σ = τ
        · subst hσ; simp [ws]
        · simp [ws, hσ, Function.update_of_ne hσ]
      have hE := Formalism.IndefR.Eqv.KerDiag.mult_equiv θ M J χ hU τ (ha τ) (ws s) ⟨_, hsm τ⟩
        (by simp only [hws])
      have hmul : iotaX X h (atTau θ (D.sp.Y 0) τ (a τ)) * gs s = gs (insert τ s) := by
        refine Prod.ext (funext fun v => ?_) ?_
        · simp only [gs, Prod.fst_mul, Pi.mul_apply]
          by_cases hv : v = X.pl.symm τ
          · subst hv
            have hm : X.pl (X.pl.symm τ) ∈ insert τ s := by simp
            have hn : X.pl (X.pl.symm τ) ∉ s := by simpa using hτ
            rw [if_pos hm, if_neg hn, hb τ, mul_one]
          · have hpv : X.pl v ≠ τ := fun e => hv (by rw [← e, Equiv.symm_apply_apply])
            rw [hoth v hv, one_mul]
            simp [Finset.mem_insert, hpv]
        · simp only [gs, Prod.snd_mul, he2, mul_one]
      rw [hupd, hE]
      show U v₀ ((iotaX X h).symm (x * gs (insert τ s)) * t) =
        U (ws s) ((iotaX X h).symm x * t * atTau θ (D.sp.Y 0) τ (a τ))
      rw [mul_assoc, ← GlobalTheory.HeckeParts.comm_atTau ht τ (a τ), ← mul_assoc]
      have hι : (iotaX X h).symm x * atTau θ (D.sp.Y 0) τ (a τ) =
          (iotaX X h).symm (x * iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))) := by
        rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
      rw [hι, ← ih U hU, mul_assoc, hmul]
  have eu : gs Finset.univ = (g, 1) := Prod.ext (funext fun v => by simp [gs]) rfl
  refine ⟨a, ha, hb, ws Finset.univ, fun τ => by simp [ws], fun U hU x => ?_⟩
  rw [← key Finset.univ U hU x, eu]

theorem coef_eq {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) (hCV : ConjVec X h θ M v₀) (g : X.B.I.Ginf)
    (a : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ)
    (ha : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ))
    (hb : ∀ τ, (iotaX X h (atTau θ (D.sp.Y 0) τ (a τ))).1 (X.pl.symm τ) = g (X.pl.symm τ))
    (w : M.Vec) (hw : ∀ τ, (w τ : M.H τ) = M.rep τ (a τ) (v₀ τ : M.H τ)) :
    ∏ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = Formalism.L2.SG.ProjRows.mInf X.B.I X.B.σ X.B.w g := by
  obtain ⟨c, hc1, hc2⟩ := hCV
  have e : ∀ τ, ⟪(w τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ =
      ⟪X.B.w (X.pl.symm τ), X.B.σ (X.pl.symm τ) (uMat (g (X.pl.symm τ))) (X.B.w (X.pl.symm τ))⟫_ℂ := by
    intro τ
    rw [← inner_antiunitary_swap (c τ) (v₀ τ : M.H τ) (w τ : M.H τ), hw τ,
      hc1 τ (a τ) (ha τ), hb τ, hc2 τ]
  simp_rw [e]
  exact Fintype.prod_equiv X.pl.symm _ _ (fun _ => rfl)

end GlobalTheory.Core.Mi.SeeHH

open GlobalTheory.Core.Mi.SeeHH in

theorem GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → ∀ T ∈ MultT θ M J χ, ∀ φ : L2X X, (φ : X.B.I.GA → ℂ) =ᵐ[muX X] evS X h t (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX X := by
  intro hP D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hCV T hT φ hφ
  obtain ⟨-, -, -, -, -, hL⟩ := GlobalTheory.T.discreteSeriesTestData_of_noncompactGaps D X hGap
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hIdE
  have hTm : PiTensorProduct.lift.symm T ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h θ S M J χ t hθ hMat T hT (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (T (PiTensorProduct.tprod ℂ v₀)) x =
      (PiTensorProduct.lift.symm T) v₀ ((iotaX X h).symm x * t) := fun x => rfl
  generalize PiTensorProduct.lift.symm T = U at hTm hfx
  generalize evS X h t (T (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hφ hfx
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t U hTm U hTm
  have hv₀ : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    obtain ⟨c, -, hc2⟩ := hCV
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : M.H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h θ M J χ t hMat.1 hR v₀ g
    have hco := coef_eq X h θ M v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (U w ((iotaX X h).symm x * t)) * U v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh U hTm x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
