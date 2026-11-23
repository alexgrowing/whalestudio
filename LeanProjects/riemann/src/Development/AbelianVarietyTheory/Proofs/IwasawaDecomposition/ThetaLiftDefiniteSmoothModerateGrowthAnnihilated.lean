import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaLiftContinuousInvariantHasDerivAtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftSmooth

theorem lift_growth (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (θ : InfFam D) (hθ : IsInfFam θ) (hS : ∀ τ, (gramAt D S τ).PosDef)
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (F : GA D S → X) (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ N : ℕ, ∀ L : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ x : GA D T,
      ∃ c : ℝ, ∀ g ∈ GinfC T, ‖lift om ν 𝓕 (fun h => L (F h)) (x * g)‖ ≤ c * normInf θ T g ^ N := by
  obtain ⟨N, hN⟩ := GlobalTheory.ThetaGrowth.thetaKO_growth ψ S T χS χT om hW θ hθ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D S ν 𝓕 ⟨hν, h𝓕⟩).2
  refine ⟨N, fun L hL x => ?_⟩
  let b := Module.finBasis ℂ X
  choose c hc using fun j => hN (L (b j)) (hL _) x C hC
  have hco : ∀ j, ∃ M : ℝ, ∀ h ∈ C, ‖b.repr (F h) j‖ ≤ M := fun j =>
    hC.exists_bound_of_continuousOn
      (((b.coord j).continuous_of_finiteDimensional.comp hF).continuousOn)
  choose M hM using hco
  refine ⟨(∑ j, M j * c j) * ν.real 𝓕, fun g hg => ?_⟩
  have key : ∀ h, ‖thetaKO om h (x * g) (L (F h))‖ ≤ (∑ j, M j * c j) * normInf θ T g ^ N := by
    intro h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    have hinv := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hW (L (F k)) (hL _)).2 γ hγ 1
      (one_mem _) k (x * g)
    rw [one_mul] at hinv
    rw [hFi γ hγ, hinv]
    have e : thetaKO om k (x * g) (L (F k)) = ∑ j, b.repr (F k) j * thetaKO om k (x * g) (L (b j)) := by
      conv_lhs => rw [← b.sum_repr (F k)]
      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM j k hk) (hc j k hk g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM j k hk))
  calc _ ≤ (∑ j, M j * c j) * normInf θ T g ^ N * ν.real 𝓕 :=
        norm_setIntegral_le_of_norm_le_const hfin fun h _ => key h
    _ = _ := by ring

theorem lift_smooth_growth_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn T θ (lift om ν 𝓕 fun h => L (F h)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth T θ (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ τ (Z : Mt T.rank), (∀ x h, RderC θ T τ Z (fun g => thetaKO om h g (L x)) = 0) → RderC θ T τ Z (lift om ν 𝓕 fun h => L (F h)) = 0 := by
  intro D ψ S T χS χT om hW θ hθ hS X _ _ _ L hL F hF hFi ν 𝓕 hν h𝓕
  have hder := fun (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) =>
    GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt D ψ S T χS χT om hW θ hθ hS X L hL F hF hFi ν 𝓕 hν h𝓕
  refine ⟨?_, ?_, ?_⟩
  · refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T
      {φ | ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ φ = lift om ν 𝓕 fun h => L' (F h)}
      ?_ ?_ _ ⟨L, hL, rfl⟩
    · rintro φ ⟨L', hL', rfl⟩
      exact (hder L' hL').1.1
    · rintro φ ⟨L', hL', rfl⟩ τ Y hY
      obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 τ Y hY
      exact ⟨_, ⟨L'', h1, rfl⟩, h3⟩
  · obtain ⟨N, hN⟩ := lift_growth D ψ S T χS χT om hW θ hθ hS X F hF hFi ν 𝓕 hν h𝓕
    refine ⟨N, fun l hl x => ?_⟩
    have hw : ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧
        List.foldr (fun p f => Rder θ T p.1 p.2 f) (lift om ν 𝓕 fun h => L (F h)) l
          = lift om ν 𝓕 fun h => L' (F h) := by
      induction l with
      | nil => exact ⟨L, hL, rfl⟩
      | cons p l ih =>
        obtain ⟨L', hL', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 p.1 p.2 (hl p List.mem_cons_self)
        refine ⟨L'', h1, ?_⟩
        rw [List.foldr_cons, e]
        exact funext fun g => (h3 g).deriv
    obtain ⟨L', hL', e⟩ := hw
    rw [e]
    exact hN L' hL' x
  · intro τ Z hZ
    obtain ⟨hY₁, hY₂⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
    obtain ⟨L₁, -, a₁, b₁⟩ := (hder L hL).2 τ _ hY₁
    obtain ⟨L₂, -, a₂, b₂⟩ := (hder L hL).2 τ _ hY₂
    funext g
    have hp : ∀ h, thetaKO om h g (L₁ (F h)) = -Complex.I * thetaKO om h g (L₂ (F h)) := by
      intro h
      have := congrFun (hZ (F h) h) g
      simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [(a₁ (F h) h g).deriv, (a₂ (F h) h g).deriv] at this
      linear_combination this
    simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [(b₁ g).deriv, (b₂ g).deriv]
    simp only [lift, hp, integral_const_mul]
    ring

end GlobalTheory.DefLiftSmooth
