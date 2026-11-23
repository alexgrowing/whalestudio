import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

noncomputable section

open GlobalTheory.ArchSch
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzHadamard

section Param

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

def dSnd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × Y → E) : ℝ × Y → (Y →L[ℝ] E) :=
  fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ Y)

omit [FiniteDimensional ℝ Y] in
theorem contDiff_dSnd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Y → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (dSnd F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ Y] in
theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Y → E} (hF : ContDiff ℝ ∞ F)
    (s : ℝ) (x : Y) : HasFDerivAt (fun x => F (s, x)) (dSnd F (s, x)) x :=
  (hF.differentiable (by simp) (s, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)

theorem hasFDerivAt_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × Y → E}
    (hF : ContDiff ℝ ∞ F) (x : Y) :
    HasFDerivAt (fun x => ∫ s in (0 : ℝ)..1, F (s, x)) (∫ s in (0 : ℝ)..1, dSnd F (s, x)) x := by
  haveI : ProperSpace Y := FiniteDimensional.proper_real Y
  have hc : Continuous (dSnd F) := (contDiff_dSnd hF).continuous
  obtain ⟨C, hC⟩ := ((isCompact_uIcc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_closedBall x 1)).exists_bound_of_continuousOn hc.continuousOn
  have c1 : ∀ y, Continuous fun s : ℝ => F (s, y) := fun y => hF.continuous.comp (by fun_prop)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x s => F (s, x))
    (F' := fun x s => dSnd F (s, x)) (s := Metric.closedBall x 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (c1 y).aestronglyMeasurable) ((c1 x).intervalIntegrable _ _)
    (hc.comp (by fun_prop : Continuous fun s : ℝ => (s, x))).aestronglyMeasurable
    (Eventually.of_forall fun s hs y hy => hC (s, y) ⟨Set.uIoc_subset_uIcc hs, hy⟩) intervalIntegrable_const
    (Eventually.of_forall fun s _ y _ => hasFDerivAt_slice hF s y)

theorem smooth_bound (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × Y → E),
    ContDiff ℝ ∞ F → ContDiff ℝ n (fun x => ∫ s in (0 : ℝ)..1, F (s, x)) ∧
      ∀ (x : Y) (w C : ℝ), 0 ≤ w → (∀ s ∈ Set.Icc (0 : ℝ) 1, w * ‖iteratedFDeriv ℝ n (fun x => F (s, x)) x‖ ≤ C) →
        w * ‖iteratedFDeriv ℝ n (fun x => ∫ s in (0 : ℝ)..1, F (s, x)) x‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ F hF
    refine ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasFDerivAt_integral hF a).continuousAt),
      fun x w C hw h => ?_⟩
    simp only [norm_iteratedFDeriv_zero] at h ⊢
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun s => w • F (s, x)) (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [norm_smul, Real.norm_of_nonneg hw]
        exact h s (Set.Ioc_subset_Icc_self hs))
    rw [intervalIntegral.integral_smul, norm_smul, Real.norm_of_nonneg hw] at h1
    simpa using h1
  | succ n ih =>
    intro E _ _ F hF
    obtain ⟨h1, h2⟩ := ih _ (dSnd F) (contDiff_dSnd hF)
    have e : fderiv ℝ (fun x => ∫ s in (0 : ℝ)..1, F (s, x)) = fun x => ∫ s in (0 : ℝ)..1, dSnd F (s, x) :=
      funext fun a => (hasFDerivAt_integral hF a).fderiv
    refine ⟨?_, fun x w C hw h => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv, e]
      exact ⟨fun a => (hasFDerivAt_integral hF a).differentiableAt, by simp, h1⟩
    · rw [← norm_iteratedFDeriv_fderiv, e]
      refine h2 x w C hw fun s hs => ?_
      have e' : fderiv ℝ (fun x => F (s, x)) = fun x => dSnd F (s, x) :=
        funext fun a => (hasFDerivAt_slice hF s a).fderiv
      have := h s hs
      rwa [← norm_iteratedFDeriv_fderiv, e'] at this

theorem exists_schwartz_average {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (K : 𝓢(Z, ℂ))
    (B₀ B₁ : Y →L[ℝ] Z) (c : ℝ) (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ c * ‖(B₀ + s • B₁) x‖) (hc0 : 0 ≤ c) :
    ∃ g : 𝓢(Y, ℂ), ∀ x, g x = ∫ s in (0 : ℝ)..1, K ((B₀ + s • B₁) x) := by
  have hF : ContDiff ℝ ∞ (fun p : ℝ × Y => K ((B₀ + p.1 • B₁) p.2)) := by
    refine (K.smooth ⊤).comp ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    fun_prop
  refine ⟨⟨fun x => ∫ s in (0 : ℝ)..1, K ((B₀ + s • B₁) x),
    contDiff_infty.2 fun n => (smooth_bound n ℂ _ hF).1, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨c ^ k * SchwartzMap.seminorm ℝ k n K * (‖B₀‖ + ‖B₁‖) ^ n, fun x => ?_⟩
  refine (smooth_bound n ℂ _ hF).2 x _ _ (by positivity) fun s hs => ?_
  set B := B₀ + s • B₁ with hB
  have hn : ‖B‖ ≤ ‖B₀‖ + ‖B₁‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right B (K.smooth ⊤) x (i := n) (by exact_mod_cast le_top)
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (K ∘ B) x‖ ≤ _
  rw [h]
  calc _ ≤ (c * ‖B x‖) ^ k * (‖iteratedFDeriv ℝ n K (B x)‖ * ∏ _j : Fin n, ‖B‖) := by
        gcongr
        · exact hc s hs x
        · exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = c ^ k * (‖B x‖ ^ k * ‖iteratedFDeriv ℝ n K (B x)‖) * ‖B‖ ^ n := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ _ := by
        gcongr
        exact SchwartzMap.le_seminorm ℝ k n K _

end Param

section Box

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem norm_iteratedFDeriv_comp_le (e : A →L[ℝ] B) (he : ‖e‖ ≤ 1) (f : 𝓢(B, ℂ)) (i : ℕ) (x : A) :
    ‖iteratedFDeriv ℝ i (fun y => f (e y)) x‖ ≤ ‖iteratedFDeriv ℝ i f (e x)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right e (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (e y)) = (f ∘ e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (e x)‖ * ∏ _j : Fin i, ‖e‖
      ≤ ‖iteratedFDeriv ℝ i f (e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => he
    _ = _ := mul_one _

theorem exists_schwartz_prod (f₁ : 𝓢(A, ℂ)) (f₂ : 𝓢(B, ℂ)) :
    ∃ f : 𝓢(A × B, ℂ), ∀ x, f x = f₁ x.1 * f₂ x.2 := by
  have hs₁ : ContDiff ℝ ∞ (fun y : A × B => f₁ y.1) := (f₁.smooth ⊤).comp contDiff_fst
  have hs₂ : ContDiff ℝ ∞ (fun y : A × B => f₂ y.2) := (f₂.smooth ⊤).comp contDiff_snd
  refine ⟨⟨fun x => f₁ x.1 * f₂ x.2, hs₁.mul hs₂, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ k i f₁ * SchwartzMap.seminorm ℝ 0 (n - i) f₂ +
      SchwartzMap.seminorm ℝ 0 i f₁ * SchwartzMap.seminorm ℝ k (n - i) f₂), fun x => ?_⟩
  have hx : ‖x‖ ^ k ≤ ‖x.1‖ ^ k + ‖x.2‖ ^ k := by
    rw [Prod.norm_def]
    have p1 := pow_nonneg (norm_nonneg x.1) k
    have p2 := pow_nonneg (norm_nonneg x.2) k
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : A × B => f₁ y.1 * f₂ y.2) x‖
      ≤ (‖x.1‖ ^ k + ‖x.2‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ x.1‖ * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_comp_le (ContinuousLinearMap.fst ℝ A B) (ContinuousLinearMap.norm_fst_le ..) f₁ i x
        · exact norm_iteratedFDeriv_comp_le (ContinuousLinearMap.snd ℝ A B) (ContinuousLinearMap.norm_snd_le ..) f₂
            (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x.1‖ ^ k * ‖iteratedFDeriv ℝ i f₁ x.1‖) * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖ +
           ‖iteratedFDeriv ℝ i f₁ x.1‖ * (‖x.2‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₁ _ _
        · exact SchwartzMap.le_seminorm ℝ k (n - i) f₂ _

end Box

section Main

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_schwartz_zero_eq_one [FiniteDimensional ℝ Y] : ∃ g : 𝓢(Y, ℂ), g 0 = 1 := by
  let b : ContDiffBump (0 : Y) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : ContDiff ℝ ∞ (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h2 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h2.toSchwartzMap h1, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simp [b])]
  simp

theorem exists_hadamard [FiniteDimensional ℝ Y] (P : Submodule ℝ Y) (f : 𝓢(Y, ℂ)) (hf : ∀ p ∈ P, f p = 0) :
    ∃ (r : ℕ) (L : Fin r → Y →L[ℝ] ℝ) (g : Fin r → 𝓢(Y, ℂ)), (∀ j, ∀ p ∈ P, L j p = 0) ∧
      ∀ x, f x = ∑ j, (L j x : ℂ) * g j x := by
  obtain ⟨q, hq⟩ := LinearMap.exists_leftInverse_of_injective P.subtype (Submodule.ker_subtype P)
  let π : Y →L[ℝ] Y := LinearMap.toContinuousLinearMap (LinearMap.id - P.subtype ∘ₗ q)
  have hπ : ∀ x, π x = x - (q x : Y) := fun x => rfl
  have hπP : ∀ p ∈ P, π p = 0 := fun p hp => by
    have := LinearMap.congr_fun hq ⟨p, hp⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [hπ, this, sub_self]
  let e := Module.finBasis ℝ Y
  let L : Fin (Module.finrank ℝ Y) → Y →L[ℝ] ℝ := fun j =>
    LinearMap.toContinuousLinearMap (e.coord j ∘ₗ (π : Y →ₗ[ℝ] Y))
  have hL : ∀ j x, L j x = e.repr (π x) j := fun j x => rfl
  obtain ⟨χ, hχ⟩ := exists_schwartz_zero_eq_one (Y := Y)
  obtain ⟨H, hH⟩ := exists_schwartz_prod f χ
  let B₀ : Y →L[ℝ] Y × Y := ContinuousLinearMap.inl ℝ Y Y
  let B₁ : Y →L[ℝ] Y × Y := (-π).prod π
  have hB : ∀ (s : ℝ) x, (B₀ + s • B₁) x = (x - s • π x, s • π x) := fun s x => by
    simp [B₀, B₁, sub_eq_add_neg]
  have hlow : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ 2 * ‖(B₀ + s • B₁) x‖ := fun s _ x => by
    rw [hB]
    have h1 := norm_fst_le (x - s • π x, s • π x)
    have h2 := norm_snd_le (x - s • π x, s • π x)
    have h3 := norm_add_le (x - s • π x) (s • π x)
    rw [sub_add_cancel] at h3
    simp only at h1 h2
    linarith
  let K : Fin (Module.finrank ℝ Y) → 𝓢(Y × Y, ℂ) := fun j => LineDeriv.lineDerivOpCLM ℂ 𝓢(Y × Y, ℂ) ((e j, -e j) : Y × Y) H
  have hK : ∀ j z, K j z = fderiv ℝ H z (e j, -e j) := fun j z => by
    simp only [K, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  choose g hg using fun j => exists_schwartz_average (K j) B₀ B₁ 2 hlow zero_le_two
  refine ⟨_, L, g, fun j p hp => by rw [hL, hπP p hp]; simp, fun x => ?_⟩
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -H ((B₀ + s • B₁) x))
      (∑ j, (L j x : ℂ) * K j ((B₀ + s • B₁) x)) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => (B₀ + s • B₁) x) (B₁ x) s := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      simpa using ((hasDerivAt_id s).smul_const (B₁ x)).const_add (B₀ x)
    have h2 := ((H.differentiable _).hasFDerivAt.comp_hasDerivAt s h1).neg
    refine h2.congr_deriv ?_
    have h3 : -(B₁ x) = ∑ j, L j x • ((e j, -e j) : Y × Y) := by
      have h4 : ∑ j, L j x • e j = π x := e.sum_repr (π x)
      ext
      · simp [B₁, Prod.fst_sum, h4]
      · simp [B₁, Prod.snd_sum, h4]
    rw [← map_neg, h3, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hK, Complex.real_smul]
  have hcK : ∀ j, Continuous fun s : ℝ => K j ((B₀ + s • B₁) x) := fun j => by
    refine (K j).continuous.comp ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) (fun s _ => hd s)
    ((continuous_finset_sum _ fun j _ => continuous_const.mul (hcK j)).intervalIntegrable _ _)
  rw [intervalIntegral.integral_finset_sum (f := fun j s => (L j x : ℂ) * K j ((B₀ + s • B₁) x)) fun j _ =>
    (continuous_const.mul (hcK j)).intervalIntegrable _ _] at hI
  simp only [intervalIntegral.integral_const_mul, ← hg] at hI
  rw [hI, hB, hB, hH, hH]
  have h5 : f (x - π x) = 0 := hf _ (by rw [hπ, sub_sub_cancel]; exact (q x).2)
  simp [h5, hχ]

open Complex GlobalTheory.CharFormDeriv in

theorem apply_linear_mul (T : 𝓢(Y, ℂ) →L[ℂ] ℂ) (L : Y →L[ℝ] ℝ)
    (hT : ∀ t : ℝ, ∀ f f' : 𝓢(Y, ℂ), (∀ x, f' x = Complex.exp ((I * t) * (L x : ℂ)) * f x) → T f' = T f)
    (f g : 𝓢(Y, ℂ)) (hg : ∀ x, g x = (L x : ℂ) * f x) : T g = 0 := by
  let ft : ℝ → 𝓢(Y, ℂ) := fun t =>
    SchwartzMap.smulLeftCLM ℂ (fun x : Y => Complex.exp ((I * t) * (L x : ℂ))) f
  have hft : ∀ t x, ft t x = Complex.exp ((I * t) * (L x : ℂ)) * f x := fun t x => by
    simp only [ft, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L t), smul_eq_mul]
  have hTft : ∀ t : ℝ, T (ft t) = T f := fun t => hT t f (ft t) (hft t)
  let u : ℝ → 𝓢(Y, ℂ) := fun t => (t : ℂ)⁻¹ • (ft t - f) - I • g
  have hu : ∀ t : ℝ, ∀ x, u t x = rem t (L x) * f x := fun t x => by
    simp only [u, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hft, hg, rem, smul_eq_mul]
    ring
  have hTu : ∀ t : ℝ, T (u t) = -I * T g := fun t => by
    simp only [u, map_sub, map_smul, hTft, sub_self, smul_zero, smul_eq_mul, zero_sub]
    ring
  have hlim : Tendsto u (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    rw [(schwartz_withSeminorms ℂ Y ℂ).tendsto_nhds u 0]
    rintro ⟨k, n⟩ ε hε
    set K := 3 * 2 ^ n * (1 + ‖L‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hδ : 0 < min 1 (ε / (K + 1)) := lt_min one_pos (div_pos hε (by linarith))
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ), self_mem_nhdsWithin] with t ht ht0
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have ht0' : t ≠ 0 := ht0
    have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
    have htε : |t| < ε / (K + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    rw [sub_zero]
    show SchwartzMap.seminorm ℂ k n (u t) < ε
    calc SchwartzMap.seminorm ℂ k n (u t) ≤ |t| * K := seminorm_rem_mul_le L f (u t) ht0' ht1 (hu t) k n
      _ ≤ |t| * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  have hcont : Tendsto (fun t => T (u t)) (nhdsWithin 0 {0}ᶜ) (nhds (T 0)) :=
    (T.continuous.tendsto 0).comp hlim
  have hconst : Tendsto (fun t => T (u t)) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (-I * T g)) := by
    simp only [hTu]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst hcont
  rw [map_zero, neg_mul, neg_eq_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left Complex.I_ne_zero

end Main

theorem eq_of_eqOn : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (P : Submodule ℝ Y)
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, (∀ p ∈ P, L p = 0) → ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, (∀ p ∈ P, f p = g p) → ℓ f = ℓ g := by
  intro Y _ _ _ P ℓ h f g hfg
  obtain ⟨r, L, u, hL, hu⟩ := exists_hadamard P (f - g) fun p hp => by
    rw [SchwartzMap.sub_apply, hfg p hp, sub_self]
  let v : Fin r → 𝓢(Y, ℂ) := fun j => SchwartzMap.smulLeftCLM ℂ (fun x => ((L j x : ℝ) : ℂ)) (u j)
  have hv : ∀ j x, v j x = (L j x : ℂ) * u j x := fun j x => by
    have htg : Function.HasTemperateGrowth fun x : Y => ((L j x : ℝ) : ℂ) :=
      (Complex.ofRealCLM.comp (L j)).hasTemperateGrowth
    simp only [v, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
  have e : f - g = ∑ j, v j := by
    ext x
    rw [hu, SchwartzMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => (hv j x).symm
  rw [← sub_eq_zero, ← map_sub, e, map_sum]
  refine Finset.sum_eq_zero fun j _ => apply_linear_mul ℓ (L j) (fun t a b hab => ?_) (u j) (v j) (hv j)
  refine h ((-t / (2 * Real.pi)) • (L j : Y →ₗ[ℝ] ℝ)) (fun p hp => by simp [hL j p hp]) a b (funext fun x => ?_)
  rw [hab, ech]
  congr 2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul]
  push_cast
  field_simp

end GlobalTheory.SchwartzHadamard
