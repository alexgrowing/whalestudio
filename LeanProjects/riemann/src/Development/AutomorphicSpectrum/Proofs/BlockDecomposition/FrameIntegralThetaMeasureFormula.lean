import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueIntegrable
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

variable {D : D7}

theorem trM_actW_ratTup (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    trM (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((trM X).map (incA D)) := by
  ext i a
  rfl

def framesEquiv (V : HSp D) {r : ℕ} (T : Matrix (Fin r) (Fin r) D.host.E) :
    framesE D.sp.cm.sig V.gram T ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = T} where
  toFun X := ⟨trM X.1, (trM_mem_framesE_iff V X.1 T).1 X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (trM_mem_framesE_iff V _ T).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem glue : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  intro D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  have hν' : HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν := hν
  have h𝓕' : HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν 𝓕 := h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hcm (AF D.host.F)
  have := hB r V.rank
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have htr : Continuous (trM : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → Mx D V.rank r) :=
    continuous_pi fun i => continuous_pi fun a =>
      (show Continuous fun X : Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E => X a i from
        (continuous_apply i).comp (continuous_apply a))
  set S := framesE D.sp.cm.sig V.gram β.1 with hS
  set Φ : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => φ (trM X) with hΦdef
  have hΦ : Measurable Φ := (hcont.comp htr).measurable
  have hν0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have hinvtop : (ν 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hν0
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have habs' : ∫⁻ g in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν < ⊤ := by
    have e := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
    simp only [hL.descend_mk] at e
    rw [← e]
    exact habs
  have hle : ∀ g : GA D V, ∑' X : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram g⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) (X : Fin r → Fin V.rank → D.host.E)))‖ₑ ≤
      GlobalTheory.SiegelFormula.absTheta V φ g := fun g => by
    have hinj : Function.Injective fun X : S => trM (X : Fin r → Fin V.rank → D.host.E) :=
      fun X Y h => (framesEquiv V β.1).injective (Subtype.ext h)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V g ξ)‖ₑ))
    simp only [hΦdef, trM_actW_ratTup, GlobalTheory.SiegelFormula.invPt]
  have hint : Integrable Φ (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 S) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S _ hΦ.enorm]
    exact ENNReal.mul_lt_top hinvtop.lt_top ((lintegral_mono hle).trans_lt habs')
  refine ⟨hint, ?_⟩
  rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_int D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S Φ hΦ hint]
  have hInv := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(Matrix.rank_mul_eq_right_of_isUnit_det _ _
        ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hth : ∀ g : GA D V, HeckeCharacterZeroLocus.SiegelWeilU.thetaS _ _ D.sp.cm.sig V.rank V.gram Φ S g =
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V g x.1) := fun g => by
    refine (tsum_congr fun X => ?_).trans ((framesEquiv V β.1).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V g x.1))
    exact congrArg φ (trM_actW_ratTup V g X.1)
  rw [IfrB, average_eq, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
  have e1 : ∀ g : GA D V, descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) (GlobalTheory.AutomorphicL2Unitary.mk (GQ V) g) =
      HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S g :=
    fun g => (hInv.descend_mk g).trans (hth g).symm
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
