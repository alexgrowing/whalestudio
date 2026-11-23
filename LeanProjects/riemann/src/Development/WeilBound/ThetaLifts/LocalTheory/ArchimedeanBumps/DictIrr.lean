import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ExistsDensity
import Development.WeilBound.ThetaLifts.SchwartzMoments.DenseC
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ContDiff

def WeakInt : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (α : Type) [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α) (G : α → SchwartzMap V ℂ), Continuous G →
    (∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ) →
    ∃ f : SchwartzMap V ℂ, ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Integrable (fun a => T (G a)) μ ∧ T f = ∫ a, T (G a) ∂μ

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ex (L : V →L[ℝ] ℝ) (x : V) : ℂ := Complex.exp (Complex.I * (L x : ℝ))

theorem ex_temp (L : V →L[ℝ] ℝ) : (ex L).HasTemperateGrowth :=
  GlobalTheory.CompanionTheory.AdelicHeis.temperate_exp_I.comp L.hasTemperateGrowth

theorem ex_deriv (L : V →L[ℝ] ℝ) (i : ℕ) (x : V) : ‖iteratedFDeriv ℝ i (ex L) x‖ ≤ ‖L‖ ^ i := by
  have h := L.iteratedFDeriv_comp_right (f := fun t : ℝ => Complex.exp (Complex.I * t)) (n := ∞)
    GlobalTheory.CompanionTheory.AdelicHeis.temperate_exp_I.1 x (i := i) (by exact_mod_cast le_top)
  have e : ex L = (fun t : ℝ => Complex.exp (Complex.I * t)) ∘ L := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, GlobalTheory.CompanionTheory.AdelicHeis.iteratedDeriv_exp_I, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

theorem semi_mul (g : 𝓢(V, ℂ)) (k j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : V → ℂ) (B : ℝ), u.HasTemperateGrowth → 0 ≤ B →
    (∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ B * (1 + ‖x‖)) →
    SchwartzMap.seminorm ℂ k j (SchwartzMap.smulLeftCLM ℂ u g) ≤ B * C := by
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ k (j - i) g + SchwartzMap.seminorm ℂ (k + 1) (j - i) g), by positivity, fun u B hu hB h => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity) fun x => ?_
  rw [SchwartzMap.smulLeftCLM_apply hu]
  have h1 := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hu.1 (g.smooth ⊤) x (n := j) (by exact_mod_cast le_top)
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h2 := h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) x
  have h3 := SchwartzMap.le_seminorm ℂ k (j - i) g x
  have h4 := SchwartzMap.le_seminorm ℂ (k + 1) (j - i) g x
  calc ‖x‖ ^ k * ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖)
      ≤ ‖x‖ ^ k * ((j.choose i : ℝ) * (B * (1 + ‖x‖)) * ‖iteratedFDeriv ℝ (j - i) g x‖) := by gcongr
    _ = B * ((j.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (j - i) g x‖ + ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) g x‖)) := by
        ring
    _ ≤ _ := by gcongr

theorem cont_mod (g : 𝓢(V, ℂ)) : Continuous fun L : V →L[ℝ] ℝ => SchwartzMap.smulLeftCLM ℂ (ex L) g := by
  refine continuous_iff_continuousAt.2 fun L₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  obtain ⟨C, hC, h⟩ := semi_mul (SchwartzMap.smulLeftCLM ℂ (ex L₀) g) k j
  have ht : Tendsto (fun L : V →L[ℝ] ℝ => ‖L - L₀‖) (𝓝 L₀) (𝓝 0) := tendsto_norm_sub_self L₀
  have ht' : Tendsto (fun L : V →L[ℝ] ℝ => ‖L - L₀‖ * C) (𝓝 L₀) (𝓝 0) := by simpa using ht.mul_const C
  filter_upwards [ht.eventually (gt_mem_nhds one_pos), ht'.eventually (gt_mem_nhds hε)] with L h1 h2
  have hu : (ex (L - L₀) - fun _ => 1).HasTemperateGrowth := (ex_temp _).sub (Function.HasTemperateGrowth.const _)
  have e : SchwartzMap.smulLeftCLM ℂ (ex L) g - SchwartzMap.smulLeftCLM ℂ (ex L₀) g =
      SchwartzMap.smulLeftCLM ℂ (ex (L - L₀) - fun _ => 1) (SchwartzMap.smulLeftCLM ℂ (ex L₀) g) := by
    ext x
    simp only [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (ex_temp _), SchwartzMap.smulLeftCLM_apply_apply hu,
      Pi.sub_apply, smul_eq_mul]
    simp only [ex]
    have : Complex.exp (Complex.I * (L x : ℝ)) = Complex.exp (Complex.I * ((L - L₀) x : ℝ)) * Complex.exp (Complex.I * (L₀ x : ℝ)) := by
      rw [← Complex.exp_add]; congr 1; simp only [ContinuousLinearMap.sub_apply]; push_cast; ring
    rw [this, sub_mul, one_mul, mul_assoc]
  rw [SchwartzMap.schwartzSeminormFamily_apply, e]
  refine (h _ _ hu (norm_nonneg _) fun i _ x => ?_).trans_lt h2
  rcases i with _ | i
  · rw [norm_iteratedFDeriv_zero]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (((L - L₀).le_opNorm x).trans ?_)
    gcongr; linarith
  · rw [iteratedFDeriv_sub_apply ((ex_temp _).1.of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i), Pi.zero_apply, sub_zero]
    refine (ex_deriv _ _ x).trans ?_
    rw [pow_succ, mul_comm]
    gcongr
    exact (pow_le_one₀ (norm_nonneg _) h1.le).trans (by linarith [norm_nonneg x])

end

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

theorem kill_mul (hS : WeakInt) (l : 𝓢(X, ℂ) →L[ℂ] ℂ) (g : 𝓢(X, ℂ))
    (h : ∀ L, l (SchwartzMap.smulLeftCLM ℂ (ex L) g) = 0) (φ : 𝓢(X, ℂ)) : l (SchwartzMap.smulLeftCLM ℂ φ g) = 0 := by
  borelize X
  obtain ⟨a, ha⟩ := exists_density φ
  let Λ : X →L[ℝ] X →L[ℝ] ℝ := (2 * Real.pi) • innerSL ℝ
  have hc : Continuous fun η => a η • SchwartzMap.smulLeftCLM ℂ (ex (Λ η)) g :=
    a.continuous.smul ((cont_mod g).comp Λ.continuous)
  obtain ⟨f, hf⟩ := hS X X volume _ hc fun k j => by
    obtain ⟨C, hC, hb⟩ := semi_mul g k j
    have ht : (fun η : X => (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2) ^ j).HasTemperateGrowth := by fun_prop
    refine Integrable.mono' (((SchwartzMap.smulLeftCLM ℂ (fun η : X => (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2) ^ j) a).integrable.norm).mul_const
      (2 ^ j * C)) (((schwartz_withSeminorms ℂ X ℂ).continuous_seminorm (k, j)).comp hc).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (apply_nonneg _ _), map_smul_eq_mul, SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    have h1 : ‖Λ η‖ ≤ 2 * (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2) := by
      nlinarith [Λ.le_opNorm η, sq_nonneg (‖Λ‖ * ‖η‖ - 1), sq_nonneg (‖Λ‖ * ‖η‖)]
    have h0 : (1 : ℝ) ≤ 2 * (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2) := by nlinarith [sq_nonneg (‖Λ‖ * ‖η‖)]
    have := hb (ex (Λ η)) ((2 * (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2)) ^ j) (ex_temp _) (by positivity) fun i hi x =>
      (ex_deriv _ i x).trans (((pow_le_pow_left₀ (norm_nonneg _) h1 i).trans (pow_le_pow_right₀ h0 hi)).trans
        (le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg x])))
    calc _ ≤ ‖a η‖ * ((2 * (1 + ‖Λ‖ ^ 2 * ‖η‖ ^ 2)) ^ j * C) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have e : SchwartzMap.smulLeftCLM ℂ φ g = f := by
    ext x
    have : f x = ∫ η, (a η • SchwartzMap.smulLeftCLM ℂ (ex (Λ η)) g) x :=
      (hf ((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X ℂ))).2
    simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (ex_temp _), smul_eq_mul] at this
    rw [this, SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, smul_eq_mul, ha, ← integral_mul_const]
    congr 1
    funext η
    have : ch ⟪η, x⟫ = ex (Λ η) x := by
      change _ = Complex.exp (Complex.I * ((2 * Real.pi * ⟪η, x⟫ : ℝ) : ℂ))
      rw [ch]
      congr 1; push_cast; ring
    rw [this]; ring
  rw [e, (hf l).2]
  simp [h]

theorem irr_inner (hS : WeakInt) (l : 𝓢(X, ℂ) →L[ℂ] ℂ) (g : 𝓢(X, ℂ)) (hg : g ≠ 0)
    (h : ∀ L a, l (SchwartzMap.smulLeftCLM ℂ (ex L) (SchwartzMap.compSubConstCLM ℂ a g)) = 0) : l = 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  refine ContinuousLinearMap.coeFn_injective (l.continuous.ext_on PositivityTheory.ThKOwn.dense_compactSupport continuous_const
    fun φ hφ => ?_)
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover (fun a : X => {x | g (x - a) ≠ 0})
    (fun a => isOpen_ne_fun (g.continuous.comp (continuous_id.sub continuous_const)) continuous_const)
    fun x _ => mem_iUnion.2 ⟨x - y, by simpa using hy⟩
  let W : X → ℂ := fun x => ∑ a ∈ t, starRingEnd ℂ (g (x - a)) * g (x - a)
  have hW : ∀ x ∈ tsupport φ, W x ≠ 0 := fun x hx => by
    obtain ⟨a, ha, hx'⟩ := mem_iUnion₂.1 (ht hx)
    have : W x = ((∑ a ∈ t, Complex.normSq (g (x - a)) : ℝ) : ℂ) := by
      simp only [W, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_ne_zero]
    exact (Finset.sum_pos' (f := fun a => Complex.normSq (g (x - a))) (fun _ _ => Complex.normSq_nonneg _) ⟨a, ha, Complex.normSq_pos.2 hx'⟩).ne'
  have hs : ∀ a, ContDiff ℝ ∞ fun x => g (x - a) := fun a => (g.smooth ⊤).comp (contDiff_id.sub contDiff_const)
  have hc : ∀ a, ContDiff ℝ ∞ fun x => starRingEnd ℂ (g (x - a)) := fun a => Complex.conjCLE.contDiff.comp (hs a)
  have hWs : ContDiff ℝ ∞ W := ContDiff.sum fun a _ => (hc a).mul (hs a)
  have hsup : ∀ a, HasCompactSupport fun x => φ x * (starRingEnd ℂ (g (x - a)) * (W x)⁻¹) := fun a => hφ.mul_right
  have hsm : ∀ a, ContDiff ℝ ∞ fun x => φ x * (starRingEnd ℂ (g (x - a)) * (W x)⁻¹) := fun a =>
    contDiff_iff_contDiffAt.2 fun x => by
      by_cases hx : x ∈ tsupport φ
      · exact (φ.smooth ⊤).contDiffAt.mul ((hc a).contDiffAt.mul (hWs.contDiffAt.inv (hW x hx)))
      · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
        rw [hy]; simp
  have e : φ = ∑ a ∈ t, SchwartzMap.smulLeftCLM ℂ ((hsup a).toSchwartzMap (hsm a)) (SchwartzMap.compSubConstCLM ℂ a g) := by
    ext x
    rw [SchwartzMap.sum_apply]
    simp only [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _), SchwartzMap.compSubConstCLM_apply,
      smul_eq_mul, HasCompactSupport.toSchwartzMap_toFun]
    by_cases hx : x ∈ tsupport φ
    · have : ∀ a, φ x * (starRingEnd ℂ (g (x - a)) * (W x)⁻¹) * g (x - a) =
          φ x * (W x)⁻¹ * (starRingEnd ℂ (g (x - a)) * g (x - a)) := fun a => by ring
      simp only [this, ← Finset.mul_sum]
      rw [mul_assoc, inv_mul_cancel₀ (hW x hx), mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  change l φ = 0
  rw [e, map_sum]
  exact Finset.sum_eq_zero fun a _ => kill_mul hS l _ (fun L => h L a) _

theorem irr (hS : WeakInt) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (l : 𝓢(V, ℂ) →L[ℂ] ℂ) (g : 𝓢(V, ℂ)) (hg : g ≠ 0)
    (h : ∀ L a, l (SchwartzMap.smulLeftCLM ℂ (ex L) (SchwartzMap.compSubConstCLM ℂ a g)) = 0) : l = 0 := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ e.symm
  have hPQ : ∀ f, P (Q f) = f := fun f => by ext x; simp [P, Q]
  have := irr_inner hS (l.comp P) (Q g) (fun h0 => hg (by rw [← hPQ g, h0, map_zero])) fun L a => by
    rw [ContinuousLinearMap.comp_apply, ← h (L.comp (e : V →L[ℝ] _)) (e.symm a)]
    congr 1
    ext x
    simp [P, Q, SchwartzMap.smulLeftCLM_apply_apply (ex_temp _), SchwartzMap.compSubConstCLM_apply, ex]
  ext f
  rw [← hPQ f]
  exact DFunLike.congr_fun this (Q f)

end PositivityTheory.ThKG.Loc.Bump

end
