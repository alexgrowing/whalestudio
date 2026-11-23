import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticSolutions

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem smulLeftCLM_delta (θ : 𝓢(E, ℂ)) (x₀ : E) :
    smulLeftCLM ℂ (θ : E → ℂ) (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) =
      θ x₀ • (TemperedDistribution.delta x₀ : 𝓢'(E, ℂ)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, TemperedDistribution.delta_apply, smul_apply,
    TemperedDistribution.delta_apply, SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]

theorem smulLeft_comm_eq {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} (hT : IsLocal T) (θ : 𝓢(E, ℂ))
    {ψ ψ₁ : 𝓢(E, ℂ)} {V : Set E} (hV : IsOpen V) (hψ₁ : ∀ x ∈ V, ψ₁ x = 1)
    (hψ : tsupport (ψ : E → ℂ) ⊆ V) (u : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ u) =
      smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) := by
  have hz : Distribution.IsVanishingOn (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) V := by
    have h2 := isVanishingOn_neg (isVanishingOn_smulLeftCLM_sub ψ₁.hasTemperateGrowth hψ₁ u)
    rwa [neg_sub] at h2
  have hc : Distribution.IsVanishingOn (comm T θ (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) V :=
    isLocal_comm hT θ V hV _ hz
  have h0 := smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth hc hψ
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

theorem pderiv_congr {n : ℕ} {α : Fin n → ℕ} {f f' : EuclideanSpace ℝ (Fin n) → ℂ}
    {x : EuclideanSpace ℝ (Fin n)} (h : f =ᶠ[nhds x] f') : pderiv α f x = pderiv α f' x := by
  rw [pderiv, pderiv, (h.iteratedFDeriv ℝ (mabs α)).eq_of_nhds]

end Helpers

section Comm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem memSobolev_zero_distribution (t : ℝ) : MemSobolev t 2 (0 : 𝓢'(E, ℂ)) := by
  have := SobolevSpace.memSobolev_toDistribution (0 : SobolevSpace E ℂ t)
  rwa [SobolevSpace.toDistribution_zero] at this

theorem exists_contDiff_comm {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} (hT : IsLocal T) (θ : 𝓢(E, ℂ)) {k : ℝ}
    (hc : HasOrder (comm T θ) k) {u : 𝓢'(E, ℂ)} {Ω' : Set E} (hΩ' : IsOpen Ω')
    {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω')
    (hu : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω' → u φ = ∫ x, φ x • g x)
    (hcover : ∀ y, y ∈ Ω' ∨ ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
      Distribution.IsVanishingOn (comm T θ u) V) :
    ∃ β : E → ℂ, ContDiff ℝ ∞ β ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ →
      comm T θ u φ = ∫ x, φ x • β x := by
  suffices hloc : ∀ y ∈ (Set.univ : Set E), ∃ ψ : 𝓢(E, ℂ), (∀ᶠ x in nhds y, ψ x = 1) ∧
      ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) (comm T θ u)) by
    obtain ⟨β, hβ, hrep⟩ := exists_contDiffOn_of_locally_memSobolev isOpen_univ hloc
    exact ⟨β, contDiffOn_univ.1 hβ, fun φ hφ ↦ hrep φ hφ (Set.subset_univ _)⟩
  intro y _
  rcases hcover y with hy | hy
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ' y hy
    have hr : 0 < ε / 8 := by positivity
    have h3 : 0 < 3 * (ε / 8) := by positivity
    have h34 : 3 * (ε / 8) < 7 * (ε / 16) := by linarith
    set ψ₁ := bumpG y h3 h34
    have hψ₁Ω : tsupport (ψ₁ : E → ℂ) ⊆ Ω' := (tsupport_bumpG y h3 h34).trans fun x hx ↦
      hball (by rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)
    have hψ₁c : HasCompactSupport (ψ₁ : E → ℂ) :=
      IsCompact.of_isClosed_subset (isCompact_closedBall y _) (isClosed_tsupport _)
        (tsupport_bumpG y h3 h34)

    have hψ₁u : smulLeftCLM ℂ (ψ₁ : E → ℂ) u =
        ((cutMul hΩ' hg ψ₁ hψ₁c hψ₁Ω : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by
      ext φ
      rw [smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
      have hc' : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (ψ₁ : E → ℂ) φ : E → ℂ) := by
        rw [SchwartzMap.smulLeftCLM_apply ψ₁.hasTemperateGrowth]
        exact hψ₁c.smul_right
      have hs' : tsupport (SchwartzMap.smulLeftCLM ℂ (ψ₁ : E → ℂ) φ : E → ℂ) ⊆ Ω' := by
        rw [SchwartzMap.smulLeftCLM_apply ψ₁.hasTemperateGrowth]
        exact (tsupport_smul_subset_left (ψ₁ : E → ℂ) (φ : E → ℂ)).trans hψ₁Ω
      rw [hu _ hc' hs']
      congr 1; ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply ψ₁.hasTemperateGrowth, cutMul_apply, smul_eq_mul,
        smul_eq_mul, smul_eq_mul]
      ring
    refine ⟨bump y hr, ?_, fun t ↦ ?_⟩
    · filter_upwards [Metric.ball_mem_nhds y hr] with x hx
      exact bump_eq_one y hr (Metric.ball_subset_closedBall hx)
    · rw [smulLeft_comm_eq hT θ (ψ₁ := ψ₁) (V := Metric.ball y (3 * (ε / 8))) Metric.isOpen_ball
        (fun x hx ↦ bumpG_eq_one y h3 h34 (Metric.ball_subset_closedBall hx))
        ((tsupport_bump y hr).trans (Metric.closedBall_subset_ball (by linarith))), hψ₁u]
      refine memSobolev_smulLeft _ ?_
      exact hc.memSobolev' (s := t + k) (by ring) (cutMul hΩ' hg ψ₁ hψ₁c hψ₁Ω).memSobolev
  · obtain ⟨V₀, hV₀, hyV, hZ⟩ := hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV₀ y hyV
    have hr : 0 < ε / 4 := by positivity
    refine ⟨bump y hr, ?_, fun t ↦ ?_⟩
    · filter_upwards [Metric.ball_mem_nhds y hr] with x hx
      exact bump_eq_one y hr (Metric.ball_subset_closedBall hx)
    · rw [smulLeftCLM_eq_zero_of_isVanishingOn (bump y hr).hasTemperateGrowth hZ
        ((tsupport_bump y hr).trans fun x hx ↦ hball (by
          rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith))]
      exact memSobolev_zero_distribution t

end Comm

section Parametrix

variable {n : ℕ}

theorem exists_parametrix {m : ℕ} (hn : 0 < n) (hm : 1 ≤ m) (hnm : n < 2 * m)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, ContDiffOn ℝ ∞ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {x₀ : EuclideanSpace ℝ (Fin n)} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hx₀U : x₀ ∈ U) (hUΩ : U ⊆ Ω) :
    ∃ E β : EuclideanSpace ℝ (Fin n) → ℂ, Integrable E ∧ HasCompactSupport E ∧ tsupport E ⊆ U ∧
      ContDiffOn ℝ ∞ E {x₀}ᶜ ∧ ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ U ∧
      ∀ φ : EuclideanSpace ℝ (Fin n) → ℂ, ContDiffOn ℝ ∞ φ U →
        ∫ x, E x * diffOp A a φ x = φ x₀ - ∫ x, β x * φ x := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)

  obtain ⟨r, hr, hrU, b, hb⟩ := exists_schwartz_coeff hU (fun α hα ↦ (ha α hα).mono hUΩ) hx₀U
  have hell' : ∀ y ∈ Metric.closedBall x₀ r, IsEllipticAt (opST A b) m y := fun y hy ↦
    isEllipticAt_opST A b hA y fun ξ hξ ↦ by
      have e : ∑ α ∈ A with mabs α = m, b α y * (mpow α ξ : ℂ) = prinSymbol A a m y ξ :=
        Finset.sum_congr rfl fun α hα ↦ by rw [hb α (Finset.mem_filter.1 hα).1 y hy]
      rw [e]
      exact hell y (hUΩ (hrU ((Metric.closedBall_subset_closedBall (by linarith)) hy))) ξ hξ
  have hx₀r : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le

  have hnm' : (n : ℝ) < 2 * m := by exact_mod_cast hnm
  have hfin : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by simp
  have ht : -((m : ℝ) + (n : ℝ) / 2) / 2 < -(Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) / 2 := by
    rw [hfin]; linarith
  have htm : (0 : ℝ) ≤ -((m : ℝ) + (n : ℝ) / 2) / 2 + m := by linarith
  obtain ⟨r₁, hr₁, E₀, hE₀, hvan⟩ := (hell' x₀ hx₀r).exists_local_solution hm ht
  obtain ⟨ρ, hρ, hρr₁, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧ ρ ≤ r :=
    ⟨min r₁ r, lt_min hr₁ hr, min_le_left _ _, min_le_right _ _⟩

  set Ω' := Metric.ball x₀ ρ \ {x₀}
  have hΩ' : IsOpen Ω' := Metric.isOpen_ball.sdiff isClosed_singleton
  have hΩ'r : Ω' ⊆ Metric.closedBall x₀ r := fun y hy ↦
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρr hy.1)
  obtain ⟨g, hg, hgrep⟩ := contDiffOn_of_isEllipticAt hm hΩ' (fun y hy ↦ hell' y (hΩ'r hy)) hE₀
    (F := 0) memSobolev_zero_distribution (by
      rw [sub_zero]
      have h1 := hvan.mono (show Ω' ⊆ Metric.ball x₀ r₁ from fun y hy ↦
        Metric.ball_subset_ball hρr₁ hy.1)
      have h2 := (TemperedDistribution.isVanishingOn_delta x₀).mono
        (show Ω' ⊆ {x₀}ᶜ from fun y hy ↦ hy.2)
      have := isVanishingOn_add h1 h2
      rwa [sub_add_cancel] at this)

  obtain ⟨e, he⟩ := memSobolev_zero_iff.1 (hE₀.mono htm)
  have hE₀e : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), E₀ φ = ∫ x, φ x • e x := fun φ ↦ by
    rw [he, MeasureTheory.Lp.toTemperedDistribution_apply]
  have he_loc : LocallyIntegrable (e : EuclideanSpace ℝ (Fin n) → ℂ) volume :=
    (Lp.memLp e).locallyIntegrable (by norm_num)

  have hae : ∀ᵐ x, x ∈ Ω' → e x = g x := by
    have h := hΩ'.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (f := fun x ↦ e x - g x)
      (he_loc.locallyIntegrableOn _ |>.sub (hg.continuousOn.locallyIntegrableOn hΩ'.measurableSet))
      fun g' hg' hg'c hg'Ω ↦ by
        have hc₁ : HasCompactSupport (Complex.ofRealCLM ∘ g') := hg'c.comp_left rfl
        have hc₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g') := by fun_prop
        obtain ⟨φ, hφdef⟩ : ∃ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), φ = hc₁.toSchwartzMap hc₂ :=
          ⟨_, rfl⟩
        have hφf : (φ : EuclideanSpace ℝ (Fin n) → ℂ) = Complex.ofRealCLM ∘ g' := by
          rw [hφdef]; rfl
        have hφ : ∀ x, φ x = (g' x : ℂ) := fun x ↦ by rw [hφf]; rfl
        have hφc : HasCompactSupport (φ : EuclideanSpace ℝ (Fin n) → ℂ) := by rw [hφf]; exact hc₁
        have hφΩ : tsupport (φ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ Ω' := by
          rw [hφf]; exact (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) _).trans hg'Ω
        have hi1 : Integrable (fun x ↦ φ x • e x) :=
          integrable_smul_of_locallyIntegrableOn (he_loc.locallyIntegrableOn _) hφc
            (Set.subset_univ _)
        have hi2 := integrable_smul_of_tsupport_subset hΩ' hg.continuousOn hφc hφΩ
        have e1 : ∫ x, g' x • (e x - g x) = (∫ x, φ x • e x) - ∫ x, φ x • g x := by
          rw [← integral_sub hi1 hi2]
          congr 1; ext x
          rw [hφ, smul_sub, Complex.real_smul, Complex.real_smul, smul_eq_mul, smul_eq_mul]
        rw [e1, ← hE₀e, ← hgrep φ hφc hφΩ, sub_self]
    filter_upwards [h] with x hx hxΩ
    exact sub_eq_zero.1 (hx hxΩ)

  have hq1 : 0 < ρ / 4 := by positivity
  have hq2 : ρ / 4 < ρ / 2 := by linarith
  set θ := bumpG x₀ hq1 hq2
  have hθs : tsupport (θ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ Metric.closedBall x₀ (ρ / 2) :=
    tsupport_bumpG x₀ hq1 hq2
  have hθ0 : ∀ x, x ∉ Metric.closedBall x₀ (ρ / 2) → θ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθs h)
  have hθx₀ : θ x₀ = 1 := bumpG_eq_one x₀ hq1 hq2 (Metric.mem_closedBall_self hq1.le)
  have hhalfU : Metric.closedBall x₀ (ρ / 2) ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU

  set E : EuclideanSpace ℝ (Fin n) → ℂ := fun x ↦ θ x * g x
  have hEs : tsupport E ⊆ Metric.closedBall x₀ (ρ / 2) :=
    (tsupport_mul_subset_left).trans hθs
  have hEc : HasCompactSupport E :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x₀ _) (isClosed_tsupport _) hEs
  have hEe : E =ᵐ[volume] fun x ↦ θ x * e x := by
    have hx₀ : ∀ᵐ x : EuclideanSpace ℝ (Fin n), x ≠ x₀ := by
      rw [ae_iff]; simp only [not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton x₀
    filter_upwards [hae, hx₀] with x hx hxx₀
    by_cases hxb : x ∈ Metric.ball x₀ ρ
    · simp only [E]; rw [hx ⟨hxb, hxx₀⟩]
    · have : x ∉ Metric.closedBall x₀ (ρ / 2) := by
        intro h; apply hxb; rw [Metric.mem_closedBall] at h; rw [Metric.mem_ball]; linarith
      simp only [E, hθ0 x this, zero_mul]
  have hEint : Integrable E := by
    have h := (θ.memLp 2 volume).integrable_mul (Lp.memLp e)
    exact h.congr hEe.symm
  have hEsmooth : ContDiffOn ℝ ∞ E {x₀}ᶜ := by
    refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    by_cases hxb : x ∈ Metric.ball x₀ ρ
    · refine ⟨Ω', hΩ', ⟨hxb, hx⟩, ?_⟩
      exact (θ.smooth'.contDiffOn.mul hg).mono Set.inter_subset_right
    · refine ⟨(Metric.closedBall x₀ (ρ / 2))ᶜ, Metric.isClosed_closedBall.isOpen_compl, ?_, ?_⟩
      · intro h; apply hxb; rw [Metric.mem_closedBall] at h; rw [Metric.mem_ball]; linarith
      · refine (contDiffOn_const (c := (0 : ℂ))).congr fun y hy ↦ ?_
        simp only [E, hθ0 y hy.2, zero_mul]

  have hT'loc : IsLocal (opST A b) := (hell' x₀ hx₀r).isLocal
  have hZ1 : Distribution.IsVanishingOn (comm (opST A b) θ E₀) (Metric.ball x₀ (ρ / 4)) := by
    have hθE : Distribution.IsVanishingOn (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ - E₀)
        (Metric.ball x₀ (ρ / 4)) := isVanishingOn_smulLeftCLM_sub θ.hasTemperateGrowth
      (fun x hx ↦ bumpG_eq_one x₀ hq1 hq2 (Metric.ball_subset_closedBall hx)) E₀
    have hθT : Distribution.IsVanishingOn
        (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) - opST A b E₀)
        (Metric.ball x₀ (ρ / 4)) := isVanishingOn_smulLeftCLM_sub θ.hasTemperateGrowth
      (fun x hx ↦ bumpG_eq_one x₀ hq1 hq2 (Metric.ball_subset_closedBall hx)) _
    have h1 := hT'loc _ Metric.isOpen_ball _ hθE
    rw [map_sub] at h1
    have e : comm (opST A b) θ E₀ = (opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) -
        opST A b E₀) - (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) -
        opST A b E₀) := by rw [comm_apply]; abel
    rw [e]
    exact isVanishingOn_sub h1 hθT
  have hZ2 : Distribution.IsVanishingOn (comm (opST A b) θ E₀) (Metric.closedBall x₀ (ρ / 2))ᶜ := by
    have hU' : IsOpen (Metric.closedBall x₀ (ρ / 2))ᶜ := Metric.isClosed_closedBall.isOpen_compl
    have h1 := (isVanishingOn_smulLeftCLM_compl θ.hasTemperateGrowth E₀).mono
      (Set.compl_subset_compl.2 hθs)
    have h2 := hT'loc _ hU' _ h1
    have h3 := (isVanishingOn_smulLeftCLM_compl θ.hasTemperateGrowth (opST A b E₀)).mono
      (Set.compl_subset_compl.2 hθs)
    rw [comm_apply]
    exact isVanishingOn_sub h2 h3
  obtain ⟨β', hβ', hβ'rep⟩ := exists_contDiff_comm hT'loc θ ((hell' x₀ hx₀r).hasOrder_comm θ) hΩ' hg
    hgrep fun y ↦ by
      by_cases hy1 : y ∈ Metric.ball x₀ (ρ / 4)
      · exact Or.inr ⟨_, Metric.isOpen_ball, hy1, hZ1⟩
      · by_cases hy2 : y ∈ Metric.closedBall x₀ (ρ / 2)
        · left
          refine ⟨Metric.closedBall_subset_ball (by linarith) hy2, fun h ↦ hy1 ?_⟩
          rw [Set.mem_singleton_iff] at h; rw [h]; exact Metric.mem_ball_self hq1
        · exact Or.inr ⟨_, Metric.isClosed_closedBall.isOpen_compl, hy2, hZ2⟩

  have hβ'0 : Set.EqOn β' 0 (Metric.closedBall x₀ (ρ / 2))ᶜ := by
    refine eqOn_of_integral_smul_eq hβ'.continuous continuous_const
      Metric.isClosed_closedBall.isOpen_compl fun φ hφc hφ ↦ ?_
    rw [← hβ'rep φ hφc, hZ2 φ hφ]
    symm
    exact integral_eq_zero_of_ae (ae_of_all _ fun x ↦ by simp [Complex.ext_iff])
  have hβ's : tsupport β' ⊆ Metric.closedBall x₀ (ρ / 2) := by
    refine closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall
    by_contra h
    exact hx (hβ'0 h)

  have hTθ : opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) =
      TemperedDistribution.delta x₀ + comm (opST A b) θ E₀ := by
    have h1 : smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) (opST A b E₀) =
        TemperedDistribution.delta x₀ := by
      have h0 := smulLeftCLM_eq_zero_of_isVanishingOn θ.hasTemperateGrowth hvan
        (hθs.trans (Metric.closedBall_subset_ball (by linarith)))
      rw [map_sub, sub_eq_zero, smulLeftCLM_delta, hθx₀, one_smul] at h0
      exact h0
    rw [comm_apply, h1]; abel
  refine ⟨E, fun x ↦ -β' x, hEint, hEc, hEs.trans hhalfU, hEsmooth, hβ'.neg, ?_, ?_, fun φ hφ ↦ ?_⟩
  · refine IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (ρ / 2)) (isClosed_tsupport _) ?_
    show tsupport (-β') ⊆ _
    rw [tsupport_neg]; exact hβ's
  · show tsupport (-β') ⊆ _
    rw [tsupport_neg]; exact hβ's.trans hhalfU

  have hq3 : 0 < 3 * ρ / 4 := by positivity
  have hq4 : 3 * ρ / 4 < ρ := by linarith
  set θ₂ := bumpG x₀ hq3 hq4
  have hθ₂U : tsupport (θ₂ : EuclideanSpace ℝ (Fin n) → ℂ) ⊆ U :=
    (tsupport_bumpG x₀ hq3 hq4).trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hrU)
  have hθ₂c : HasCompactSupport (θ₂ : EuclideanSpace ℝ (Fin n) → ℂ) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x₀ _) (isClosed_tsupport _)
      (tsupport_bumpG x₀ hq3 hq4)
  set φ' := cutMul hU hφ θ₂ hθ₂c hθ₂U
  have hφ' : ∀ x ∈ Metric.closedBall x₀ (3 * ρ / 4), φ' x = φ x := fun x hx ↦ by
    rw [cutMul_apply, bumpG_eq_one x₀ hq3 hq4 hx, one_mul]
  have hφ'c : HasCompactSupport (φ' : EuclideanSpace ℝ (Fin n) → ℂ) := by
    rw [show (φ' : EuclideanSpace ℝ (Fin n) → ℂ) = fun x ↦ θ₂ x * φ x from rfl]
    exact hθ₂c.mul_right
  set ψ' := ∑ α ∈ A, SchwartzMap.smulLeftCLM ℂ (b α : EuclideanSpace ℝ (Fin n) → ℂ) (∂^{mdir α} φ')
  have hDψ : ∀ x ∈ Metric.ball x₀ (3 * ρ / 4), diffOp A a φ x = ψ' x := by
    intro x hx
    rw [sum_smulLeft_apply_eq_diffOp A a b φ' (fun α hα ↦ hb α hα x (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith) hx)))]
    simp only [diffOp]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    congr 1
    refine pderiv_congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact (hφ' y (Metric.ball_subset_closedBall hy)).symm
  have step1 : ∫ x, E x * diffOp A a φ x = ∫ x, ψ' x • (θ x * e x) := by
    calc ∫ x, E x * diffOp A a φ x = ∫ x, ψ' x • E x := by
          congr 1; ext x
          by_cases hx : x ∈ Metric.closedBall x₀ (ρ / 2)
          · rw [hDψ x (Metric.closedBall_subset_ball (by linarith) hx), smul_eq_mul, mul_comm]
          · simp only [E, hθ0 x hx, zero_mul, mul_zero, smul_zero]
      _ = _ := integral_congr_ae (hEe.mono fun x hx ↦ by show ψ' x • E x = _; rw [hx])
  have step2 : ∫ x, ψ' x • (θ x * e x) =
      smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ ψ' := by
    rw [smulLeftCLM_apply_apply, hE₀e]
    congr 1; ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  have step3 : smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀ ψ' =
      opST A b (smulLeftCLM ℂ (θ : EuclideanSpace ℝ (Fin n) → ℂ) E₀) φ' :=
    (opST_apply_apply A b _ φ').symm
  rw [step1, step2, step3, hTθ, add_apply, TemperedDistribution.delta_apply,
    hφ' x₀ (Metric.mem_closedBall_self hq3.le), hβ'rep φ' hφ'c]
  have step4 : ∫ x, φ' x • β' x = ∫ x, φ x * β' x := by
    congr 1; ext x
    by_cases hx : x ∈ Metric.closedBall x₀ (ρ / 2)
    · rw [hφ' x (Metric.closedBall_subset_closedBall (by linarith) hx), smul_eq_mul]
    · rw [hβ'0 hx]; simp
  have e5 : ∫ x, (fun x ↦ -β' x) x * φ x = -∫ x, φ x * β' x := by
    rw [← integral_neg]; congr 1; ext x; simp only; ring
  rw [step4, e5, sub_neg_eq_add]

end Parametrix

end

end GroundTheory.Automorphic.Sobolev
