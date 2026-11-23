import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftSmooth

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t₀ 1).prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hK'c : ∀ t, Continuous (K' t) := fun t => hK'.comp (Continuous.prodMk_right t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => ‖(M : ℂ)‖)
    (Metric.ball_mem_nhds t₀ one_pos) (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'c t₀).aestronglyMeasurable ?_ hconst.norm ?_).2
  · refine Filter.Eventually.of_forall fun h t ht => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv' γ hγ]
    refine (hM (t, c) ⟨Metric.ball_subset_closedBall ht, hc⟩).trans ?_
    rw [Complex.norm_real]
    exact le_abs_self M
  · exact Filter.Eventually.of_forall fun h t _ => hd t h

theorem lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
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
