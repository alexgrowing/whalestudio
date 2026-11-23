import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarianStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.TFlatFam

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}

theorem om_split (s : StepFB ψ J B) (a : GA D J.W) (h : GA D B.V) (Φ : WO J.W B.V → ℂ) :
    s.om (a, h) Φ = s.om (a, 1) (s.om (1, h) Φ) := by
  have e : ((a, h) : GA D J.W × GA D B.V) = (a, 1) * (1, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem tFlat_eq_pairKer (hD : Descent D) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ) (hΦ : IsThetaFunO ψ J.W B.V Φ) (h₀ : GA D J.W₀)
    (h : GA D B.V) :
    tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) = pairKer s vL Y (flatFB s (s.om (1, h) Φ)) h₀ 1 := by
  have hc := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1
  rw [(embA B.d B.o).map_one, ← om_split] at hc
  have h1 : B.o.emb ((1 : GA D B.A), (1 : GA D B.L)) = 1 := B.o.emb.map_one
  rw [h1] at hc
  unfold tFlat pairKer
  rw [hc, h1]

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem star_psi_mul (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) * ψ a = 1 := by
  have h := Complex.conj_mul' (ψ a)
  rw [hψ.1.2.1 a] at h
  simpa using h

theorem pair_periodic (hψ : IsStdChar D ψ (-1)) (o : OrthDec B.V₀ B.A B.L) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (y : WO J.W₀ B.L → ℂ)
    (hy : ∀ γ w, y (ratW B.L J.W₀ γ + w) = ψ (-(symplOH J.W₀ B.L (ratW B.L J.W₀ γ) w)) * y w)
    (γ : Mx D B.L.rank J.W₀.rank) (hγ : γ ∈ ratMx D B.L.rank J.W₀.rank) (v : Mx D B.L.rank J.W₀.rank) :
    Ξ ((o.resT J.W₀).symm (0, γ + v)) * star (y (γ + v)) = Ξ ((o.resT J.W₀).symm (0, v)) * star (y v) := by
  obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
  have hmem : (o.resT J.W₀).symm (0, rat γ₀) ∈ ratL B.V₀ J.W₀ := by
    rw [o.mem_ratL_resT, AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, ⟨γ₀, rfl⟩⟩
  obtain ⟨g₀, hg₀⟩ := hmem
  have hg : ratW B.V₀ J.W₀ g₀ = (o.resT J.W₀).symm (0, rat γ₀) := hg₀
  have hsplit : (o.resT J.W₀).symm (0, rat γ₀ + v) = ratW B.V₀ J.W₀ g₀ + (o.resT J.W₀).symm (0, v) := by
    rw [hg, ← map_add, Prod.mk_add_mk, zero_add]
  have hsym : symplOH J.W₀ B.V₀ (ratW B.V₀ J.W₀ g₀) ((o.resT J.W₀).symm (0, v)) =
      symplOH J.W₀ B.L (ratW B.L J.W₀ γ₀) v := by
    rw [hg, o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
    rfl
  have hy' := hy γ₀ v
  have hrat : ratW B.L J.W₀ γ₀ = rat γ₀ := rfl
  rw [hrat] at hy'
  rw [hsplit, hΞ.quasi, hsym, hy', hrat, star_mul']
  calc ψ (-symplOH J.W₀ B.L (rat γ₀) v) * Ξ ((o.resT J.W₀).symm (0, v)) *
        (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * star (y v))
      = (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * ψ (-symplOH J.W₀ B.L (rat γ₀) v)) *
        (Ξ ((o.resT J.W₀).symm (0, v)) * star (y v)) := by ring
    _ = _ := by rw [star_psi_mul hψ, one_mul]

end GlobalTheory.Unf.FB.TFlatFam

namespace GlobalTheory.Unf.FB.TFlatFam

theorem flatFB_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (Ψ : WO J.W B.V → ℂ) :
    flatFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) 0 Ψ := rfl

theorem tFlat_eq_int {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) :
    tFlat s vL y Ψ = ∫ v in vL.𝓕, flatFB s Ψ ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := rfl

theorem main : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W B.V Φ → (Continuous fun p : GA D J.W₀ × GA D B.V => tFlat s vL (Y p.1) (s.om (J.d.emb0 p.1, p.2) Φ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h, tFlat s vL (Y (γ * h₀)) (s.om (J.d.emb0 (γ * h₀), h) Φ) = tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ∧ ∀ h, handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1 = ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
  intro D hD ψ σ J B s vL Y Φ hY hΦ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hflat : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) := fun h =>
    (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hxo, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
    have hfl := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hxo.1 Φ hΦ
    rw [hx] at hfl
    let f : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) →
        (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ :=
      fun vp => ((J.d.emb0 vp.2.1, vp.2.2), ((0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, vp.1)))
    have hf : Continuous f :=
      ((J.d.continuous_embed.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)).prodMk (continuous_const.prodMk
          ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_fst)))
    have h1 := hfl.comp hf
    let K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.V → ℂ := fun v p =>
      flatFB s (s.om (J.d.emb0 p.1, p.2) Φ) ((B.o.resT J.W₀).symm (0, v)) * star (Y p.1 v)
    have h2 : Continuous fun vp : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) => star (Y vp.2.1 vp.1) :=
      continuous_star.comp (hY.cont.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst))
    have hKc : Continuous (Function.uncurry K) := by
      have e : Function.uncurry K = fun vp => (fun q : (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ =>
          flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) q.2.1 (s.om q.1 Φ) q.2.2) (f vp) *
          star (Y vp.2.1 vp.1) := by
        funext vp
        simp only [Function.uncurry, K, f, flatFB_eq]
      rw [e]
      exact h1.mul h2
    have hKp : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ v p, K (γ + v) p = K v p := by
      intro γ hγ v p
      have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (J.d.emb0 p.1, p.2) Φ)) :=
        (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
      exact pair_periodic hψ B.o _ hΞ (Y p.1) (hY.quasi p.1) γ hγ v
    have hK := (GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D B.L.rank J.W₀.rank vL (GA D J.W₀ × GA D B.V) K hKc hKp).2.1
    simp only [tFlat_eq_int]
    exact hK
  · intro γ hγ h₀ h
    rw [tFlat_eq_pairKer hD s vL Y Φ hΦ, tFlat_eq_pairKer hD s vL Y Φ hΦ]
    exact (GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant D ψ σ J B s vL Y _ hY (hflat h)).2.1 γ hγ h₀ 1
  · intro h
    unfold handFB
    congr 1
    funext h₀
    exact (tFlat_eq_pairKer hD s vL Y Φ hΦ h₀ h).symm

end GlobalTheory.Unf.FB.TFlatFam
