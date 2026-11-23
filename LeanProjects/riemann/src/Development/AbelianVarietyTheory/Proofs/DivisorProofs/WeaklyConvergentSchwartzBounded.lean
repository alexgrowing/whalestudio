import Mathlib
open Filter Topology

namespace GlobalTheory.WeakBddSchwartz

variable {ι : Type}

lemma summable_norm_lp1 (c : lp (fun _ : ι => ℂ) 1) : Summable fun i => ‖c i‖ := by
  have h1 := (memℓp_gen_iff (p := 1) (by norm_num)).1 (lp.memℓp c)
  simpa using h1

lemma norm_lp1 (c : lp (fun _ : ι => ℂ) 1) : ‖c‖ = ∑' i, ‖c i‖ := by
  rw [lp.norm_eq_tsum_rpow (p := 1) (by norm_num)]
  simp

lemma summable_mul (c : lp (fun _ : ι => ℂ) 1) {a : ι → ℂ} {M : ℝ} (h : ∀ i, ‖a i‖ ≤ M) :
    Summable fun i => c i * a i := by
  refine Summable.of_norm_bounded ((summable_norm_lp1 c).mul_right M) (fun i => ?_)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)

lemma pair_le (c : lp (fun _ : ι => ℂ) 1) {a : ι → ℂ} {M : ℝ} (h : ∀ i, ‖a i‖ ≤ M) :
    ‖∑' i, c i * a i‖ ≤ M * ‖c‖ := by
  have hs := ((summable_norm_lp1 c).hasSum.mul_right M)
  refine (tsum_of_norm_bounded hs (fun i => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
  · rw [norm_lp1, mul_comm]

noncomputable def pair (a : ι → ℂ) (M : ℝ) (h : ∀ i, ‖a i‖ ≤ M) :
    lp (fun _ : ι => ℂ) 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun c => ∑' i, c i * a i
      map_add' := fun c d => by
        simp only [lp.coeFn_add, Pi.add_apply, add_mul]
        exact (summable_mul c h).tsum_add (summable_mul d h)
      map_smul' := fun r c => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact tsum_mul_left }
    M (fun c => pair_le c h)

lemma pair_apply (a : ι → ℂ) (M : ℝ) (h : ∀ i, ‖a i‖ ≤ M) (c : lp (fun _ : ι => ℂ) 1) :
    pair a M h c = ∑' i, c i * a i := rfl

lemma pair_single [DecidableEq ι] (a : ι → ℂ) (M : ℝ) (h : ∀ i, ‖a i‖ ≤ M) (i : ι) :
    pair a M h (lp.single 1 i 1) = a i := by
  rw [pair_apply, tsum_eq_single i]
  · simp [lp.coeFn_single]
  · intro j hj
    simp [lp.coeFn_single, Pi.single_apply, hj]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def lam (k n : ℕ) (f : SchwartzMap V ℂ) (p : V × (Fin n → V)) : ℂ :=
  ((‖p.1‖ ^ k / ∏ i, ‖p.2 i‖ : ℝ) : ℂ) * iteratedFDeriv ℝ n f p.1 p.2

lemma lam_bound (k n : ℕ) (f : SchwartzMap V ℂ) (p : V × (Fin n → V)) :
    ‖lam k n f p‖ ≤ SchwartzMap.seminorm ℂ k n f := by
  rcases p with ⟨x, m⟩
  simp only [lam, norm_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hp : ∏ i, ‖m i‖ = 0
  · simp [hp]
  · have hpos : 0 < ∏ i, ‖m i‖ := lt_of_le_of_ne (by positivity) (Ne.symm hp)
    calc (‖x‖ ^ k / ∏ i, ‖m i‖) * ‖iteratedFDeriv ℝ n f x m‖
        ≤ (‖x‖ ^ k / ∏ i, ‖m i‖) * (‖iteratedFDeriv ℝ n f x‖ * ∏ i, ‖m i‖) :=
          mul_le_mul_of_nonneg_left ((iteratedFDeriv ℝ n f x).le_opNorm m) (by positivity)
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by field_simp
      _ ≤ SchwartzMap.seminorm ℂ k n f := SchwartzMap.le_seminorm ℂ k n f x

lemma cda (n : ℕ) (f : SchwartzMap V ℂ) (x : V) : ContDiffAt ℝ n f x :=
  (f.smooth ⊤).contDiffAt.of_le (by exact_mod_cast le_top)

lemma lam_add (k n : ℕ) (f g : SchwartzMap V ℂ) (p : V × (Fin n → V)) :
    lam k n (f + g) p = lam k n f p + lam k n g p := by
  simp only [lam]
  rw [show (⇑(f + g) : V → ℂ) = ⇑f + ⇑g from rfl]
  rw [iteratedFDeriv_add_apply (cda n f p.1) (cda n g p.1)]
  simp [mul_add]

lemma lam_smul (k n : ℕ) (r : ℂ) (f : SchwartzMap V ℂ) (p : V × (Fin n → V)) :
    lam k n (r • f) p = r * lam k n f p := by
  simp only [lam]
  rw [show (⇑(r • f) : V → ℂ) = r • ⇑f from rfl]
  rw [iteratedFDeriv_const_smul_apply (cda n f p.1)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.WeakBddSchwartz

namespace GlobalTheory.WeakBddSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def testCLM (k n : ℕ) (c : lp (fun _ : V × (Fin n → V) => ℂ) 1) :
    SchwartzMap V ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => pair (lam k n f) _ (lam_bound k n f) c)
    (fun f g => by
      simp only [pair_apply, lam_add, mul_add]
      exact (summable_mul c (lam_bound k n f)).tsum_add (summable_mul c (lam_bound k n g)))
    (fun r f => by
      simp only [pair_apply, lam_smul, RingHom.id_apply, smul_eq_mul]
      rw [← tsum_mul_left]; congr 1; ext i; ring)
    ⟨{(k, n)}, ‖c‖, norm_nonneg _, fun f => by
      simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply, pair_apply]
      rw [mul_comm]
      exact pair_le c (lam_bound k n f)⟩

end GlobalTheory.WeakBddSchwartz

namespace GlobalTheory

open GlobalTheory.WeakBddSchwartz in

theorem SchwartzMap.bddAbove_seminorm_of_weak_tendsto :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      (f : ℕ → SchwartzMap V ℂ) (f₀ : SchwartzMap V ℂ),
      (∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T (f j)) atTop (𝓝 (T f₀))) →
      ∀ k n : ℕ, BddAbove (Set.range fun j => SchwartzMap.seminorm ℂ k n (f j)) := by
  intro V _ _ _ f f₀ hf k n
  classical
  let A : ℕ → lp (fun _ : V × (Fin n → V) => ℂ) 1 →L[ℂ] ℂ :=
    fun j => pair (lam k n (f j)) _ (lam_bound k n (f j))
  have hpt : ∀ c, ∃ C, ∀ j, ‖A j c‖ ≤ C := by
    intro c
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ (hf (testCLM k n c)))
    exact ⟨C, fun j => hC _ ⟨j, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpt
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨j, rfl⟩
  refine _root_.SchwartzMap.seminorm_le_bound ℂ k n (f j) (le_max_right _ _) (fun x => ?_)
  set B := max C 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hl : ∀ m : Fin n → V, ‖lam k n (f j) (x, m)‖ ≤ B := by
    intro m
    have h1 := (A j).le_opNorm (lp.single 1 (x, m) 1)
    rw [show A j (lp.single 1 (x, m) 1) = lam k n (f j) (x, m) from pair_single _ _ _ _,
      lp.norm_single (by norm_num), norm_one, mul_one] at h1
    exact h1.trans ((hC j).trans (le_max_left _ _))
  by_cases hx : ‖x‖ ^ k = 0
  · rw [hx, zero_mul]; exact hB0
  have hxpos : 0 < ‖x‖ ^ k := lt_of_le_of_ne (by positivity) (Ne.symm hx)
  rw [← le_div_iff₀' hxpos]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  by_cases hp : ∏ i, ‖m i‖ = 0
  · obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hp
    rw [(iteratedFDeriv ℝ n (f j) x).map_coord_zero i (norm_eq_zero.1 hi)]
    simp [hp]
  have hppos : 0 < ∏ i, ‖m i‖ := lt_of_le_of_ne (by positivity) (Ne.symm hp)
  have h := hl m
  simp only [lam, norm_mul, Complex.norm_real] at h
  rw [Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_iff₀ hppos] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hxpos]
  linarith [mul_comm (‖x‖ ^ k) ‖iteratedFDeriv ℝ n (f j) x m‖]

end GlobalTheory
