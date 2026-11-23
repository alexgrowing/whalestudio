import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenReal

set_option maxHeartbeats 2000000 in

theorem downInt_lie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (τ : D.what₂.Tau)
    (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ →
    ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank),
    (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) →
    ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ), (∀ g, downInt R i t y (R.ptP i t P) l g = 0) →
    ∀ g, downInt R i t y (R.ptP i t P') l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y τ Y hY P P' hder l hvan g
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hom := (hP i t).datum
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ptP i t P) := hG.core.thP.pt_theta i t P
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hom hY
  have hf' := ht.theta hf

  have hid : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y (R.ptP i t P) = R.ptP i t P' := by
    funext z
    have h1 := hd _ hf 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact h1.unique (hder z)
  rw [← hid]
  set f := R.ptP i t P with hfdef
  set f' := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y f with hf'def

  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have hrat : ∀ γ ∈ GQ (Vc D i), ∀ (c : GA D (Vc D i)) (g' : GA D (Wc D i)),
      thetaKO (R.ωP i t) (γ * c) g' f' = thetaKO (R.ωP i t) c g' f' := by
    intro γ hγ c g'
    unfold thetaKO
    have e : ((γ * c, g') : GA D (Vc D i) × GA D (Wc D i)) = ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (c, g') := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf')
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩

  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact (Vc D i) hpos
  have hΨ : Continuous fun p : GA D (Vc D i) × ℝ =>
      thetaKO (R.ωP i t) p.1 (g * oneP R.θ (Wc D i) τ Y p.2) f' * l (R.extV i t y p.1) := by
    refine Continuous.mul ?_ (hcont.comp continuous_fst)
    exact (hom.om_cont f' hf' 0).comp (continuous_fst.prodMk
      (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)))
  obtain ⟨B, hB⟩ := (hC.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hΨ.continuousOn
  have hbd : ∀ (h : GA D (Vc D i)) (x : ℝ), x ∈ Metric.ball (0 : ℝ) 1 →
      ‖thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h)‖ ≤ B := by
    intro h x hxb
    obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    subst e
    rw [hrat γ hγ c, hinv γ hγ c]
    exact hB (c, x) (Set.mk_mem_prod hc (Metric.ball_subset_closedBall hxb))

  have hfin : R.νV i t (R.fdV i t) < ⊤ := by
    haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (Vc D i)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
    have h1 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D (Vc D i)) (GQ (Vc D i)) C hC
      (fun h => by
        obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
        exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩)
      (R.νV i t) (hm.νV i t).1.1 (R.fdV i t) (hm.νV i t).2 (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h2 | h2
    · simp at h2
    · exact h2

  have hmeas : ∀ (φ : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ x : ℝ,
      AEStronglyMeasurable (fun h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) φ * l (R.extV i t y h))
        ((R.νV i t).restrict (R.fdV i t)) := fun φ hφ x =>
    (((hom.om_cont φ hφ 0).comp (continuous_id.prodMk continuous_const)).mul hcont).measurable.aestronglyMeasurable
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (R.νV i t).restrict (R.fdV i t))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (F := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f * l (R.extV i t y h))
    (F' := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h))
    (bound := fun _ => B) (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun x => hmeas f hf x)
    (GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y f l _ hf)
    (hmeas f' hf' 0) (.of_forall fun h x hxb => hbd h x hxb) (integrableOn_const hfin.ne)
    (.of_forall fun h x _ => ?_)).2
  · have e : (fun x : ℝ => ∫ h in R.fdV i t, thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f *
        l (R.extV i t y h) ∂(R.νV i t)) = fun _ => 0 := funext fun x => hvan _
    rw [e] at key
    have h0 := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at h0
    exact h0
  · refine (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g' => thetaKO (R.ωP i t) h g' f)
      (φ' := fun g' => thetaKO (R.ωP i t) h g' f') (fun g' => ?_) g x).mul_const _
    simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (h, g') 0

end GlobalTheory.DownLift.GenReal
