import ReciprocityTheory.L2DbarEstimates.SkodaWeights.HlinVsqPos
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff

theorem vsq_pos {p : ℕ} (w : Fin p → ℂ) (hw : w ≠ 0) : 0 < vsq w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := by simpa using hi
  have h1 : 0 < ‖w i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi') 2
  have h2 : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  exact lt_of_lt_of_le h1 h2

theorem smoothR_vsq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) {p : ℕ}
    (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l)) : SmoothR n z (fun x => vsq (gv g x)) := by
  unfold SmoothR Smooth
  intro e he
  have hd : ∀ l, ContDiffOn ℝ ∞ (fun y => g l (e.symm y)) e.target := by
    intro l
    have h1 : ContDiffOn ℝ ∞ (g l ∘ e.symm) e.target := Holo.smooth n z (g l) (hg l) e he
    exact h1
  have hs : ContDiffOn ℝ ∞ (fun y => ∑ l, ‖g l (e.symm y)‖ ^ 2) e.target :=
    ContDiffOn.sum (fun l _ => (contDiff_norm_sq ℂ).comp_contDiffOn (hd l))
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  simpa [Function.comp_def, vsq, gv] using h4

theorem smoothR_log (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f : M → ℝ)
    (hf : SmoothR n z f) (hpos : ∀ x, 0 < f x) : SmoothR n z (fun x => Real.log (f x)) := by
  unfold SmoothR Smooth at *
  intro e he
  have h1 := hf e he
  have h2 : ContDiffOn ℝ ∞ (fun y => f (e.symm y)) e.target := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn h1
    simpa [Function.comp_def] using h
  have h3 : ContDiffOn ℝ ∞ (fun y => Real.log (f (e.symm y))) e.target :=
    h2.log (fun y _ => (hpos _).ne')
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  simpa [Function.comp_def] using h4

private theorem eq_neg_mul_inv_sq_of_zero_eq (A B s : ℂ) (hs : s ≠ 0) (h : 0 = A * s⁻¹ + s * B) :
    B = -A * s⁻¹ ^ 2 := by
  have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  linear_combination (-(s⁻¹)) * h - B * hinv

theorem skodaDbar (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaDbarStatement n M := by
  unfold SkodaDbarStatement
  intro z hz p g u hg hu hg0 x i ξ
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
  have hus : Ck n z 1 u := Smooth.ck n z 1 _ (Holo.smooth n z _ hu)
  have hcg : ∀ l, Ck n z 1 (fun y => (starRingEnd ℂ) (g l y)) :=
    fun l => Ck.conj n z 1 _ (hgs l)
  have hS : ∀ y, ((vsq (gv g y) : ℝ) : ℂ) ≠ 0 :=
    fun y => Complex.ofReal_ne_zero.mpr (vsq_pos _ (hg0 y)).ne'
  have hSsm : Smooth n z (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := smoothR_vsq n z g hg
  have hSc : Ck n z 1 (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := Smooth.ck n z 1 _ hSsm
  have hSi : Ck n z 1 (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    apply Smooth.ck
    unfold Smooth
    intro e he
    exact (hSsm e he).inv (fun y _ => hS _)
  have hSfun : (fun y => ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => ∑ l, (starRingEnd ℂ) (g l y) * g l y := by
    funext y
    simp only [vsq, gv, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hdbS : ∀ j, db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x := by
    intro j
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) j x, db_conj, Holo.db_eq_zero n z _ (hg l) j x]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdbSi : ∀ j, db n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : db n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact db_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (db_mul n z _ _ hSc hSi j x))
  have hF : (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => u y * ((starRingEnd ℂ) (g i y) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    funext y
    rw [div_eq_mul_inv, mul_assoc]
  have hdbF : ∀ j, db n z j
      (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x =
      u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) := by
    intro j
    rw [hF, db_mul n z _ _ hus (Ck.mul n z 1 _ _ (hcg i) hSi) j x, Holo.db_eq_zero n z _ hu j x,
      db_mul n z _ _ (hcg i) hSi j x, db_conj, hdbSi j, hdbS j]
    try beta_reduce
    ring
  have hL : dbarDot n z (fun y => u y * (starRingEnd ℂ) (g i y) / ((vsq (gv g y) : ℝ) : ℂ)) x ξ =
      ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) := by
    unfold dbarDot
    exact Finset.sum_congr rfl (fun j _ => by rw [hdbF j])
  have hsplit : ∑ j, u x * ((starRingEnd ℂ) (d n z j (g i) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ + (starRingEnd ℂ) (g i x) *
        (-(∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2)) *
        (starRingEnd ℂ) (ξ j) =
      u x * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        u x * (starRingEnd ℂ) (g i x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
          ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hswap : ∑ j, (∑ l, (starRingEnd ℂ) (d n z j (g l) x) * g l x) * (starRingEnd ℂ) (ξ j) =
      ∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hconj : (starRingEnd ℂ) (perp (gv g x) (jacM n z g x ξ) i) =
      ∑ j, (starRingEnd ℂ) (d n z j (g i) x) * (starRingEnd ℂ) (ξ j) -
        (starRingEnd ℂ) (g i x) *
          (∑ l, g l x * ∑ j, (starRingEnd ℂ) (d n z j (g l) x) * (starRingEnd ℂ) (ξ j)) /
            ((vsq (gv g x) : ℝ) : ℂ) := by
    simp only [perp, jacM, gv, map_sub, map_mul, map_sum, map_div₀, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  rw [hL, hsplit, hswap, hconj]
  ring

private theorem db_log_eq_inv_mul_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (k : Fin n) (ph : M → ℝ) (hph : SmoothR n z ph) (hpos : ∀ y, 0 < ph y) (y : M) :
    db n z k (fun y => ((Real.log (ph y) : ℝ) : ℂ)) y =
      ((ph y : ℝ) : ℂ)⁻¹ * db n z k (fun y => ((ph y : ℝ) : ℂ)) y := by
  unfold db
  by_cases hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source
  · rw [dif_pos hex, dif_pos hex]
    have hs := Classical.choose_spec hex
    generalize Classical.choose hex = e at hs ⊢
    have hzy : z y = e y := hs.1 hs.2
    have hp : e y ∈ e.target := e.map_source hs.2
    have hsy : e.symm (e y) = y := e.left_inv hs.2
    have hc : ContDiffOn ℝ ∞ (fun w => ph (e.symm w)) e.target := by
      have h := Complex.reCLM.contDiff.comp_contDiffOn (hph e hs.1)
      simpa [Function.comp_def] using h
    have hd : DifferentiableAt ℝ (fun w => ph (e.symm w)) (e y) :=
      (hc.differentiableOn (by first | simp | exact WithTop.coe_le_coe.mpr le_top | norm_num)
        ).differentiableAt (e.open_target.mem_nhds hp)
    have hne : ph (e.symm (e y)) ≠ 0 := (hpos _).ne'
    have h1 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) (hd.hasFDerivAt.log hne)).fderiv
    have h2 := (Complex.ofRealCLM.hasFDerivAt.comp (e y) hd.hasFDerivAt).fderiv
    have hf1 : (fun y => ((Real.log (ph y) : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => Real.log (ph (e.symm w)) := by
      funext w
      simp
    have hf2 : (fun y => ((ph y : ℝ) : ℂ)) ∘ e.symm =
        ⇑Complex.ofRealCLM ∘ fun w => ph (e.symm w) := by
      funext w
      simp
    rw [hzy]
    unfold wdb
    rw [hf1, hf2, h1, h2, hsy]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  · rw [dif_neg hex, dif_neg hex, mul_zero]

private theorem ofReal_vsq_perp_eq {p : ℕ} (g w : Fin p → ℂ) (hS : vsq g ≠ 0) :
    ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, w l * (starRingEnd ℂ) (w l) -
      (∑ l, (starRingEnd ℂ) (g l) * w l) * (∑ l, g l * (starRingEnd ℂ) (w l)) / ((vsq g : ℝ) : ℂ) := by
  have hSc : ((vsq g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS
  have hgg : ∑ l, (starRingEnd ℂ) (g l) * g l = ((vsq g : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e1 : ((vsq (perp g w) : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (perp g w l) * perp g w l := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have e2 : ∀ l, (starRingEnd ℂ) (perp g w l) * perp g w l =
      w l * (starRingEnd ℂ) (w l) -
      ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * (g l * (starRingEnd ℂ) (w l)) -
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * w l) +
      ((∑ j, g j * (starRingEnd ℂ) (w j)) / ((vsq g : ℝ) : ℂ)) *
        ((∑ j, (starRingEnd ℂ) (g j) * w j) / ((vsq g : ℝ) : ℂ)) * ((starRingEnd ℂ) (g l) * g l) := by
    intro l
    simp only [perp, map_sub, map_mul, map_div₀, map_sum, Complex.conj_ofReal, Complex.conj_conj]
    ring
  rw [e1, Finset.sum_congr rfl (fun l _ => e2 l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hgg]
  field_simp
  ring

private theorem levi_form_expand_eq_neg_sq_mul_add_sum {n p : ℕ} (a : Fin n → Fin p → ℂ) (G : Fin p → ℂ) (ξ : Fin n → ℂ)
    (c : ℂ) :
    ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (G l) * a j l) * c ^ 2 * (∑ l, (starRingEnd ℂ) (a k l) * G l) +
      c * ∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) =
    -(c ^ 2) * ((∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j) *
      (∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j))) +
    c * ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) := by
  have h1 : ∑ l, (starRingEnd ℂ) (G l) * ∑ j, a j l * ξ j =
      ∑ j, (∑ l, (starRingEnd ℂ) (G l) * a j l) * ξ j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h2 : ∑ l, G l * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * G l) * (starRingEnd ℂ) (ξ k) := by
    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have h3 : ∑ l, (∑ j, a j l * ξ j) * (starRingEnd ℂ) (∑ j, a j l * ξ j) =
      ∑ j, ∑ k, (∑ l, (starRingEnd ℂ) (a k l) * a j l) * ξ j * (starRingEnd ℂ) (ξ k) := by
    simp only [map_sum, map_mul, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h1, h2, h3, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem skodaLevi (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaLeviStatement n M := by
  unfold SkodaLeviStatement
  intro z hz p g hg hg0 x ξ
  have hgs2 : ∀ l, Ck n z 2 (g l) := fun l => Smooth.ck n z 2 _ (Holo.smooth n z _ (hg l))
  have hgs : ∀ l, Ck n z 1 (g l) := fun l => Smooth.ck n z 1 _ (Holo.smooth n z _ (hg l))
  have hcg : ∀ l, Ck n z 1 (fun y => (starRingEnd ℂ) (g l y)) :=
    fun l => Ck.conj n z 1 _ (hgs l)
  have hS : ∀ y, ((vsq (gv g y) : ℝ) : ℂ) ≠ 0 :=
    fun y => Complex.ofReal_ne_zero.mpr (vsq_pos _ (hg0 y)).ne'
  have hSsm : Smooth n z (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := smoothR_vsq n z g hg
  have hSc : Ck n z 1 (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := Smooth.ck n z 1 _ hSsm
  have hSi : Ck n z 1 (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) := by
    apply Smooth.ck
    unfold Smooth
    intro e he
    exact (hSsm e he).inv (fun y _ => hS _)
  have hSfun : (fun y => ((vsq (gv g y) : ℝ) : ℂ)) =
      fun y => ∑ l, (starRingEnd ℂ) (g l y) * g l y := by
    funext y
    simp only [vsq, gv, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hdbS : ∀ k y, db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) y =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k y
    rw [hSfun, db_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) k y]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [db_mul n z _ _ (hcg l) (hgs l) k y, db_conj, Holo.db_eq_zero n z _ (hg l) k y]
    ring
  have hdS : ∀ j, d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x =
      ∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x := by
    intro j
    rw [hSfun, d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (g l y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (hcg l) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (hcg l) (hgs l) j x, d_conj, Holo.db_eq_zero n z _ (hg l) j x, map_zero]
    ring
  have hone : (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) =
      fun _ => (1 : ℂ) := by
    funext y
    exact mul_inv_cancel₀ (hS y)
  have hdSi : ∀ j, d n z j (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
      -(d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ)) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 := by
    intro j
    have h0 : d n z j (fun y => ((vsq (gv g y) : ℝ) : ℂ) * (((vsq (gv g y) : ℝ) : ℂ))⁻¹) x =
        0 := by
      rw [hone]
      exact d_const n z 1 j x
    exact eq_neg_mul_inv_sq_of_zero_eq _ _ _ (hS x) (h0.symm.trans (d_mul n z _ _ hSc hSi j x))
  have hE : ∀ k, Ck n z 1 (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) := by
    intro k
    have h : (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) =
        db n z k (fun y => ((vsq (gv g y) : ℝ) : ℂ)) := funext (fun y => (hdbS k y).symm)
    rw [h]
    exact Smooth.ck n z 1 _ (Smooth.db n z k _ hSsm)
  have hdg1 : ∀ k l, Ck n z 1 (d n z k (g l)) := fun k l => Ck.d n z 1 k (g l) (hgs2 l)
  have hdb0 : ∀ j l, db n z j (g l) = fun _ => 0 :=
    fun j l => funext (Holo.db_eq_zero n z _ (hg l) j)
  have hdEk : ∀ j k, d n z j (fun y => ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_finset_sum n z Finset.univ (fun l y => (starRingEnd ℂ) (d n z k (g l) y) * g l y)
      (fun l => Ck.mul n z 1 _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l)) j x]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [d_mul n z _ _ (Ck.conj n z 1 _ (hdg1 k l)) (hgs l) j x, d_conj,
      ← d_db_comm n z (g l) (hgs2 l) k j x, hdb0 j l, d_const, map_zero]
    ring
  have hdE : ∀ j k, d n z j
      (fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y) x =
      -(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
      ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x := by
    intro j k
    rw [d_mul n z _ _ hSi (hE k) j x, hdSi j, hdS j, hdEk j k]
    all_goals ring
  have hG : ∀ k, db n z k (fun y => ((Real.log (vsq (gv g y)) : ℝ) : ℂ)) =
      fun y => (((vsq (gv g y) : ℝ) : ℂ))⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) y) * g l y := by
    intro k
    funext y
    rw [db_log_eq_inv_mul_db n z k _ (smoothR_vsq n z g hg) (fun y => vsq_pos _ (hg0 y)) y, hdbS k y]
  have hLevi : Levi n z (fun y => Real.log (vsq (gv g y))) x ξ =
      ∑ j, ∑ k, (-(∑ l, (starRingEnd ℂ) (g l x) * d n z j (g l) x) * ((vsq (gv g x) : ℝ) : ℂ)⁻¹ ^ 2 *
        (∑ l, (starRingEnd ℂ) (d n z k (g l) x) * g l x) +
        ((vsq (gv g x) : ℝ) : ℂ)⁻¹ * ∑ l, (starRingEnd ℂ) (d n z k (g l) x) * d n z j (g l) x) * ξ j * (starRingEnd ℂ) (ξ k) := by
    unfold Levi
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hG k, hdE j k]
  refine (hLevi.trans (levi_form_expand_eq_neg_sq_mul_add_sum (fun j l => d n z j (g l) x) (gv g x) ξ (((vsq (gv g x) : ℝ) : ℂ)⁻¹))).trans ?_
  rw [Complex.ofReal_div, ofReal_vsq_perp_eq (gv g x) (jacM n z g x ξ) (vsq_pos _ (hg0 x)).ne']
  simp only [jacM, gv]
  ring

theorem skodaWeight (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaWeightStatement n M := by
  unfold SkodaWeightStatement
  intro z hz p g φ₀ t hg hg0 hφ hL ht
  have hpos : ∀ x, 0 < vsq (gv g x) := fun x => vsq_pos _ (hg0 x)
  have hlog : SmoothR n z (fun x => Real.log (vsq (gv g x))) :=
    smoothR_log n z _ (smoothR_vsq n z g hg) hpos
  have hconst : SmoothR n z (fun _ : M => t) := by
    unfold SmoothR Smooth
    intro e _
    exact contDiffOn_const
  have htl : SmoothR n z (fun x => t * Real.log (vsq (gv g x))) :=
    SmoothR.mul n z _ _ hconst hlog
  have hsm : SmoothR n z (skW g φ₀ t) := SmoothR.add n z _ _ hφ htl
  have hlevi : ∀ x ξ, Levi n z (skW g φ₀ t) x ξ = Levi n z φ₀ x ξ +
      (t : ℂ) * ((vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x) : ℝ) : ℂ) := by
    intro x ξ
    have e1 := levi_add n z φ₀ (fun y => t * Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 φ₀ hφ) (SmoothR.ckR n z 2 _ htl) x ξ
    have e2 := levi_const_mul n z t (fun y => Real.log (vsq (gv g y)))
      (SmoothR.ckR n z 2 _ hlog) x ξ
    have e3 := skodaLevi n M z hz p g hg hg0 x ξ
    rw [← e3, ← e2]
    exact e1
  have hre : ∀ x ξ, (Levi n z (skW g φ₀ t) x ξ).re =
      (Levi n z φ₀ x ξ).re + t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    rw [hlevi x ξ, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hq : ∀ x ξ, 0 ≤ t * (vsq (perp (gv g x) (jacM n z g x ξ)) / vsq (gv g x)) := by
    intro x ξ
    have h0 : 0 ≤ vsq (perp (gv g x) (jacM n z g x ξ)) := by
      unfold vsq
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_nonneg ht (div_nonneg h0 (hpos x).le)
  refine ⟨hsm, ?_, ?_⟩
  · unfold LeviNonneg
    intro x ξ
    rw [hre]
    exact add_nonneg (hL x ξ) (hq x ξ)
  · intro x ξ
    rw [hre]
    linarith [hL x ξ]

private theorem sum_conj_mul_perp_eq_zero {p : ℕ} (w a : Fin p → ℂ) (hw : vsq w ≠ 0) :
    ∑ j, (starRingEnd ℂ) (w j) * perp w a j = 0 := by
  have hs : ∑ j, (starRingEnd ℂ) (w j) * w j = ((vsq w : ℝ) : ℂ) := by
    simp only [vsq, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
  have hw' : ((vsq w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  have h1 : ∑ j, (starRingEnd ℂ) (w j) * perp w a j =
      ∑ j, (starRingEnd ℂ) (w j) * a j - (∑ j, (starRingEnd ℂ) (w j) * w j) *
        ((∑ j, (starRingEnd ℂ) (w j) * a j) / ((vsq w : ℝ) : ℂ)) := by
    simp only [perp]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h1, hs, mul_div_cancel₀ _ hw', sub_self]

private theorem norm_perp_apply_sq_le {p : ℕ} (w a : Fin p → ℂ) (i : Fin p) (hw : w ≠ 0) :
    ‖perp w a i‖ ^ 2 ≤ (1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a) := by
  have hW : 0 < vsq w := vsq_pos w hw
  have horth := sum_conj_mul_perp_eq_zero w a hW.ne'
  have hsplit : (starRingEnd ℂ) (w i) * perp w a i +
      ∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j = 0 :=
    (Finset.add_sum_erase Finset.univ (fun j => (starRingEnd ℂ) (w j) * perp w a j)
      (Finset.mem_univ i)).trans horth
  have hneg : (starRingEnd ℂ) (w i) * perp w a i =
      -∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j := by
    linear_combination hsplit
  have hA : ‖w i‖ * ‖perp w a i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
    calc ‖w i‖ * ‖perp w a i‖ = ‖(starRingEnd ℂ) (w i) * perp w a i‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ = ‖∑ j ∈ Finset.univ.erase i, (starRingEnd ℂ) (w j) * perp w a j‖ := by
          rw [hneg, norm_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖(starRingEnd ℂ) (w j) * perp w a j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.univ.erase i, ‖w j‖ * ‖perp w a j‖ := by
          simp only [norm_mul, Complex.norm_conj]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i) (fun j => ‖w j‖)
    (fun j => ‖perp w a j‖)
  have h0 : 0 ≤ ‖w i‖ * ‖perp w a i‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (‖w i‖ * ‖perp w a i‖) ^ 2 ≤ (∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2) *
      ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 := by
    nlinarith [mul_le_mul hA hA h0 (le_trans h0 hA), hCS]
  have hWs : ‖w i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖w j‖ ^ 2 = vsq w :=
    Finset.add_sum_erase Finset.univ (fun j => ‖w j‖ ^ 2) (Finset.mem_univ i)
  have hVs : ‖perp w a i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖perp w a j‖ ^ 2 =
      vsq (perp w a) :=
    Finset.add_sum_erase Finset.univ (fun j => ‖perp w a j‖ ^ 2) (Finset.mem_univ i)
  have h3 : vsq w * ‖perp w a i‖ ^ 2 ≤ (vsq w - ‖w i‖ ^ 2) * vsq (perp w a) := by
    rw [← hWs, ← hVs]
    nlinarith [h2]
  rw [one_sub_div hW.ne', div_mul_eq_mul_div, le_div_iff₀ hW]
  nlinarith [h3]

theorem skodaHyp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] :
    SkodaHypStatement n M := by
  unfold SkodaHypStatement
  intro z hz p g φ₀ t u hg hu hg0 hφ hL ht x i ξ
  rw [skodaDbar n M z hz p g u hg hu hg0 x i ξ]
  have hW := (skodaWeight n M z hz p g φ₀ t hg hg0 hφ hL ht.le).2.2 x ξ
  rw [show g i x = gv g x i from rfl]
  generalize (Levi n z (skW g φ₀ t) x ξ).re = L at hW ⊢
  generalize jacM n z g x ξ = a at hW ⊢
  have hw0 := hg0 x
  generalize gv g x = w at hw0 hW ⊢
  have hWp : 0 < vsq w := vsq_pos w hw0
  have hWn : vsq w ≠ 0 := hWp.ne'
  have htn : t ≠ 0 := ht.ne'
  have hn : ‖((vsq w : ℝ) : ℂ)‖ = vsq w := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWp]
  have hLHS : ‖u x * (starRingEnd ℂ) (perp w a i) / ((vsq w : ℝ) : ℂ)‖ ^ 2 =
      ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_conj, hn]
    ring
  rw [hLHS]
  have key := norm_perp_apply_sq_le w a i hw0
  have hwi : ‖w i‖ ^ 2 ≤ vsq w := by
    unfold vsq
    exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hc : 0 ≤ 1 - ‖w i‖ ^ 2 / vsq w := sub_nonneg.mpr ((div_le_one hWp).mpr hwi)
  have hU : 0 ≤ ‖u x‖ ^ 2 := by positivity
  calc ‖u x‖ ^ 2 * ‖perp w a i‖ ^ 2 / vsq w ^ 2
      ≤ ‖u x‖ ^ 2 * ((1 - ‖w i‖ ^ 2 / vsq w) * vsq (perp w a)) / vsq w ^ 2 := by
        gcongr
    _ = ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) *
          (t * (vsq (perp w a) / vsq w)) := by
        field_simp <;> ring
    _ ≤ ‖u x‖ ^ 2 * (1 - ‖w i‖ ^ 2 / vsq w) / (t * vsq w) * L :=
        mul_le_mul_of_nonneg_left hW (div_nonneg (mul_nonneg hU hc) (mul_pos ht hWp).le)

end ReciprocityTheory.L2DbarEstimates.H
