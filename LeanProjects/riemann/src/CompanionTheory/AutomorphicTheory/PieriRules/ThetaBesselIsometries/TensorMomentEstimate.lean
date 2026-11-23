import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasicStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrepDiscreteSeriesSumStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorRawOfFrepStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsKTypeNonzeroBesselStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSumDecompositionStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.FamilyDerivativeExpansion.Kap

theorem mul_mem_GG {k r : ℕ} {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  simp only [GG, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem ae_pair {k r : ℕ} {U V : Set (Mx k r)} {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn V ν) :
    ∀ᵐ p ∂(μ.prod ν), Matrix.of p.1 ∈ U ∧ Matrix.of p.2 ∈ V := by
  haveI := hμ.1
  haveI := hν.1
  have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ U := ae_iff.2 hμ.2.2.1
  have h2 : ∀ᵐ x ∂ν, Matrix.of x ∈ V := ae_iff.2 hν.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem bessel_add {k r : ℕ} {R : Rep k r} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {A A' : R.H → Wp}
    (h : IsBes R z π A) (h' : IsBes R z π A') : IsBes R z π (fun v => A v + A' v) := by
  obtain ⟨h1, h2, h3, C, Ws, hW, h4⟩ := h
  obtain ⟨h1', h2', h3', C', Ws', hW', h4'⟩ := h'
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun g hg m hm v hv => ?_, max |C| |C'|, Ws ++ Ws', ?_, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, h1' v hv w hw]; abel
  · simp only [h2 a v hv, h2' a v hv, smul_add]
  · simp only [h3 g hg m hm v hv, h3' g hg m hm v hv, map_add, smul_add]
  · intro w hw
    rcases List.mem_append.1 hw with e | e
    exacts [hW w e, hW' w e]
  · have n : ∀ L : List (List (Mx k r)), 0 ≤ (L.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w v‖).sum :=
      fun L => List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)
    rw [List.map_append, List.sum_append, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ((h4 v hv).trans ?_) ((h4' v hv).trans ?_))
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (n _)
    · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) (n _)

theorem kappa_dual : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om l hR hRI hF hT hS hom
    hl hnz I lI hlI
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hbes, hS_eq, hsm⟩ :=
    GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om hR hRI hF hT.raw hom I
  obtain ⟨-, -, -, -, hTKsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨-, -, -, hIsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε (muI I) (RI I) (hRI I)
  obtain ⟨hadj, -, hev, -⟩ := GlobalTheory.T.frep_discrete_series_sum hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hprTK⟩ := GlobalTheory.T.tensor_raw_of_frep hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw
  have key : ∀ y ∈ (RI I).sm, ∀ v ∈ R.TK, (innerSL ℂ (l v)).smulRight (l (ev Γ R om (fun c => io I c y))) =
      (ep I : ℂ) • (innerSL ℂ (lI (∑ c, pr I c (tm R om v c)))).smulRight (lI y) := by
    intro y hy v hvTK
    have htmTK : ∀ c, tm R om v c ∈ R.TK := fun c => R.TK.smul_mem _ hvTK
    have hPTK : (∑ c, pr I c (tm R om v c)) ∈ (RI I).TK :=
      Submodule.sum_mem _ fun c _ => hprTK I c _ (htmTK c)
    rw [← (hl.2 _ (hsm.mem y hy) v hvTK).2, ← (hlI.2 y hy _ hPTK).2]
    unfold be
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pair hS.2.2.2.2.1 hS.2.2.2.2.2.1] with p hp
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨_, hp.1, _, hp.2, rfl⟩
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := mul_mem_GG hp.1.1 hp.2.1
    unfold beInt
    rw [← hS_eq _ hs y hy, ← hev, hadj I _ (hIsm _ hg y hy) _ (fun c => hTKsm _ (htmTK c)), smul_smul, mul_assoc]
  have hep : (ep I : ℂ) * (ep I : ℂ) = 1 := by rcases hT.ep_sq I with e | e <;> simp [e]
  constructor
  · obtain ⟨κ₀, hκ⟩ : ∃ κ₀ : ℂ, ∀ v ∈ R.TK, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v := by
      by_cases hI : NzOn (RI I) lI
      · obtain ⟨y, hy, hy0⟩ := hI
        have hyy : ⟪lI y, lI y⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hy0
        refine ⟨star ((ep I : ℂ) * ⟪lI y, l (ev Γ R om (fun c => io I c y))⟫_ℂ / ⟪lI y, lI y⟫_ℂ), fun v hv => ?_⟩
        refine ext_inner_right ℂ fun ξ => ?_
        have h4 := congrArg (fun T : Wp →L[ℂ] Wp => ⟪lI y, T ξ⟫_ℂ) (key y hy v hv)
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
          inner_smul_right] at h4
        rw [inner_smul_left, starRingEnd_apply, star_star, div_mul_eq_mul_div, eq_div_iff hyy]
        linear_combination (-(ep I : ℂ)) * h4 - (⟪lI (∑ c, pr I c (tm R om v c)), ξ⟫_ℂ * ⟪lI y, lI y⟫_ℂ) * hep
      · refine ⟨0, fun v hv => ?_⟩
        rw [zero_smul]
        by_contra hne
        exact hI ⟨_, Submodule.sum_mem (RI I).smSub fun c _ =>
          (hT.raw.pr_sm I c).mem _ (R.smSub.smul_mem _ (hTKsm v hv)), hne⟩
    refine ⟨κ₀, fun v hv => ?_⟩
    by_contra hne
    have hB := bessel_add (hbes lI hlI.1) (Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 (-κ₀))
    obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π _ hR hB
      ⟨v, hv, fun e => hne (by simpa only [neg_smul, add_neg_eq_zero] using e)⟩
    exact hx0 (by rw [hκ x hx, neg_smul, add_neg_cancel])
  intro κ₀ hκ y hy
  obtain ⟨v, hvTK, hv0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π l hR hl.1 hnz
  have h3 := key y hy v hvTK
  rw [hκ v (hTKsm v hvTK)] at h3
  have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l v)) h3
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left] at h4
  have hne : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  apply smul_right_injective Wp hne
  simp only
  rw [h4, smul_smul, smul_smul]
  congr 1
  simp only [starRingEnd_apply]
  ring

end CompanionTheory.FamilyDerivativeExpansion.Kap
