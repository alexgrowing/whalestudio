import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefiniteStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefLiftSmooth
theorem deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hω hθ hΦ hS _ hν h𝓕 hφ k τs Xs hX h
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  set κ := GlobalTheory.Mem.Lift.thKer ψ S T om with hκ
  let L : GlobalTheory.RealWeil.thetaSub ψ S T → GA D T → ℂ := fun f h => ∫ g in 𝓕, κ f g h * φ g ∂ν
  have hkinv : ∀ f, ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T), κ f (γ * g) h * φ (γ * g) = κ f g h * φ g := by
    intro f γ hγ g h
    have := hK.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [this, hφ.left γ hγ]
  have hcont : ∀ φ' ∈ Set.range L, Continuous φ' := by
    rintro _ ⟨f, rfl⟩
    exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun h g => κ f g h * φ g) (((hK.cont f).comp continuous_swap).mul (hφ.cont.comp continuous_snd))
      (fun γ hγ h g => hkinv f γ hγ g h)
  have hder : ∀ φ' ∈ Set.range L, ∀ τ, ∀ X ∈ lieAt T τ, ∃ φ'' ∈ Set.range L, ∀ h,
      HasDerivAt (fun t : ℝ => φ' (h * oneP θ T τ X t)) (φ'' h) 0 := by
    rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hK.derW τ X hX f
    refine ⟨L f', ⟨f', rfl⟩, fun h => ?_⟩
    have hoc := GlobalTheory.Mem.Lift.continuous_oneP (V := T) hθ hX
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t g => κ f g (h * oneP θ T τ X t) * φ g) (fun t g => κ f' g (h * oneP θ T τ X t) * φ g)
      (fun t => ((hK.cont f).comp (continuous_id.prodMk continuous_const)).mul hφ.cont)
      (((hK.cont f').comp (continuous_snd.prodMk (continuous_const.mul (hoc.comp continuous_fst)))).mul
        (hφ.cont.comp continuous_snd))
      (fun γ hγ t g => hkinv f γ hγ g _) (fun γ hγ t g => hkinv f' γ hγ g _)
      (fun t g => (GlobalTheory.Mem.Lift.hasDerivAt_oneP (φ := fun h => κ f g h) (φ' := fun h => κ f' g h) hθ hX
        (fun h => e g h) h t).mul_const (φ g)) 0
    simpa only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, L] using key
  have hsm := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T (Set.range L) hcont hder (L ⟨Φ, hΦ⟩) ⟨_, rfl⟩
  exact hsm k τs Xs hX h
end GlobalTheory.DefLiftSmooth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  first | exact @_root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | exact _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | (intros; apply _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth <;> assumption)
end
