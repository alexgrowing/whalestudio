import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g h => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_le_quotHeight {θ : InfFam D} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    (hf : IsThetaFunO ψ S T f) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ g h, ‖thetaKO om g h f‖ ≤ K * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  have hb := (hC χS χT om hω μ 𝓕 hμ f hl).2
  have hK : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A := by positivity
  refine ⟨_, A, hK, fun g h => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  rw [← thetaKO_left_fst hω hf γ hγ g h, ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hf (γ * g) γ' hγ' h]
  refine (hb _ _).trans ?_
  have e : C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A =
      C * (sobO ψ θ μ 𝓕 d f).toReal * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (height_pos S _) (height_pos T _)).le
    (mul_le_mul h1 h2 (height_pos T _).le (by linarith [quotHeight_pos S g])) A) (by positivity)

end GlobalTheory.ChainOnto.ThetaSwap

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

theorem integrable_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D S)} {X : Set (GA D S)} {ν' : Measure (GA D T)}
    {X' : Set (GA D T)} (hν : ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ S) X ν) (hν' : ν'.IsHaarMeasure)
    (hX' : IsFundamentalDomain (GQ T) X' ν') {G : GA D S → ℂ} {F : GA D T → ℂ} (hG : RapidDec S G)
    (hF : RapidDec T F) :
    Integrable (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g))
      ((ν'.restrict X').prod (ν.restrict X)) := by
  obtain ⟨-, -, -, hS2, hSB⟩ := Formalism.IndefR.Eqv.ga_facts D S
  obtain ⟨-, -, -, hT2, hTB⟩ := Formalism.IndefR.Eqv.ga_facts D T
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  obtain ⟨K, A, hK, hb⟩ := thetaKO_le_quotHeight hθ hω hf
  obtain ⟨B, hB⟩ := hG.decay A
  obtain ⟨B', hB'⟩ := hF.decay A
  have hc : Continuous (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) := by
    have h1 : Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 f :=
      (hω.om_cont f hf 0).comp (continuous_snd.prodMk continuous_fst)
    exact (h1.mul (hF.continuous.comp continuous_fst)).mul
      (Complex.continuous_conj.comp (hG.continuous.comp continuous_snd))
  refine Integrable.of_bound hc.aestronglyMeasurable (K * B * B') (.of_forall fun p => ?_)
  obtain ⟨h, g⟩ := p
  have hq := (pow_pos (quotHeight_pos S g) A).le
  have hq' := (pow_pos (quotHeight_pos T h) A).le
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) hq).trans (hB g)
  calc ‖Function.uncurry (fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) (h, g)‖
        = ‖thetaKO om g h f‖ * ‖F h‖ * ‖G g‖ := by simp [Function.uncurry, norm_mul]
    _ ≤ K * (quotHeight S g * quotHeight T h) ^ A * ‖F h‖ * ‖G g‖ := by gcongr; exact hb g h
    _ = K * (‖G g‖ * quotHeight S g ^ A) * (‖F h‖ * quotHeight T h ^ A) := by ring
    _ ≤ K * B * B' := by
        gcongr
        · exact hB g
        · exact hB' h

theorem integral_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ →
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S))
    (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν →
    ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ),
    GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F →
    ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' =
      ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  intro D ψ θ S T χS χT om hθ hω f hf ν X ν' X' hν hX hν' hX' G F hG hF
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  exact integral_integral_swap (integrable_prod hθ hω hf hν hX hν' hX' hG hF)

end GlobalTheory.ChainOnto.ThetaSwap

example : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S)) (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν → ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ), GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F → ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' = ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν :=
  GlobalTheory.ChainOnto.ThetaSwap.integral_swap
