import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero

noncomputable section

open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace

namespace GlobalTheory.Chamber.DampedCone

theorem orthant {ι : Type} [Fintype ι] (c : ι → ℂ) (hc : ∀ i, (c i).re < 0) :
    Integrable (fun t : ι → ℝ => ∏ i, (Set.Ioi (0 : ℝ)).indicator (fun s : ℝ => Complex.exp (c i * s)) (t i)) ∧
    ∫ t : ι → ℝ, ∏ i, (Set.Ioi (0 : ℝ)).indicator (fun s : ℝ => Complex.exp (c i * s)) (t i) = ∏ i, -(c i)⁻¹ := by
  refine ⟨Integrable.fintype_prod (f := fun i => (Set.Ioi (0 : ℝ)).indicator fun s : ℝ => Complex.exp (c i * s))
    fun i => (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_exp_mul_complex_Ioi (hc i) 0), ?_⟩
  rw [integral_fintype_prod_volume_eq_prod
    (fun i => (Set.Ioi (0 : ℝ)).indicator fun s : ℝ => Complex.exp (c i * s))]
  refine prod_congr rfl fun i _ => ?_
  rw [integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi (hc i) 0]
  simp [neg_div]

theorem volume_eq_smul_map {V ι : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V) :
    (volume : Measure V) = ENNReal.ofReal (√(Matrix.gram ℝ b).det) •
      Measure.map b.equivFunL.symm (volume : Measure (ι → ℝ)) := by
  let o : OrthonormalBasis ι ℝ V := (stdOrthonormalBasis ℝ V).reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  have h1 : Measure.map b.equivFunL.symm (volume : Measure (ι → ℝ)) = b.addHaar := by
    have h : (volume : Measure (ι → ℝ)) = (Pi.basisFun ℝ ι).addHaar := by
      rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]
    rw [h, Module.Basis.map_addHaar]
    congr 1
    ext i
    show b.equivFun.symm (Pi.basisFun ℝ ι i) = b i
    simp [Pi.single_apply]
  have h2 : (Matrix.gram ℝ b).det = (o.toBasis.det b) ^ 2 := by
    have : Matrix.gram ℝ b = (o.toBasis.toMatrix b).transpose * o.toBasis.toMatrix b := by
      ext i j
      simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← o.sum_inner_mul_inner]
      exact sum_congr rfl fun x _ => by rw [real_inner_comm]
    rw [this, Matrix.det_mul, Matrix.det_transpose, Module.Basis.det_apply, sq]
  rw [h1, h2, Real.sqrt_sq_eq_abs, ← Measure.addHaar_parallelepiped, o.addHaar_eq_volume, Module.Basis.addHaar_def,
    ← Module.Basis.coe_parallelepiped]
  exact Measure.addHaarMeasure_unique _ _

theorem cone {k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (V : Submodule ℝ (A0 k)) (f g : ι → A0 k) (Z l m : A0 k)
    (hZ : Z ∈ V) (hg : ∀ i, g i ∈ V) (hdim : Fintype.card ι = Module.finrank ℝ V)
    (h0 : ∀ i j, i ≠ j → ⟪f i, g j⟫_ℝ = 0) (h1 : ∀ i, 0 < ⟪f i, g i⟫_ℝ) (hm : ∀ i, 0 < ⟪m, g i⟫_ℝ)
    (F : V → ℂ) (hF : ∀ H : V, (∀ i, 0 < ⟪f i, H - Z⟫_ℝ) → F H = eLC l m H)
    (hF' : ∀ H : V, ¬ (∀ i, 0 < ⟪f i, H - Z⟫_ℝ) → F H = 0) :
    Integrable F ∧ ∫ H, F H = (√(Matrix.gram ℝ g).det : ℝ) *
      (∏ i, -(Complex.I * (⟪l, g i⟫_ℝ : ℝ) - (⟪m, g i⟫_ℝ : ℝ))⁻¹) * eLC l m Z := by
  have key : ∀ (t : ι → ℝ) i, ⟪f i, ∑ j, t j • g j⟫_ℝ = t i * ⟪f i, g i⟫_ℝ := fun t i => by
    rw [inner_sum, sum_eq_single i (fun j _ h => by rw [real_inner_smul_right, h0 i j h.symm, mul_zero]) (by simp),
      real_inner_smul_right]
  let g' : ι → V := fun i => ⟨g i, hg i⟩
  have li : LinearIndependent ℝ g' := Fintype.linearIndependent_iff.2 fun t ht i => by
    have := key t i
    rw [show ∑ j, t j • g j = 0 by simpa [g'] using congrArg Subtype.val ht, inner_zero_right] at this
    exact (mul_eq_zero.1 this.symm).resolve_right (h1 i).ne'
  have sp : ⊤ ≤ Submodule.span ℝ (Set.range g') := (li.span_eq_top_of_card_eq_finrank' hdim).ge
  let b : Module.Basis ι ℝ V := Module.Basis.mk li sp
  have hb : ∀ t : ι → ℝ, ((b.equivFunL.symm t : V) : A0 k) = ∑ j, t j • g j := fun t => by
    show ((b.equivFun.symm t : V) : A0 k) = _
    simp [b, g', Module.Basis.equivFun_symm_apply]
  have hgram : Matrix.gram ℝ b = Matrix.gram ℝ g := by
    ext i j
    simp [b, g']
  let c : ι → ℂ := fun i => Complex.I * (⟪l, g i⟫_ℝ : ℝ) - (⟪m, g i⟫_ℝ : ℝ)
  obtain ⟨i1, i2⟩ := orthant c fun i => by simpa [c] using hm i
  let e : (ι → ℝ) ≃ᵐ V := b.equivFunL.symm.toHomeomorph.toMeasurableEquiv
  have hv : (volume : Measure V) = ENNReal.ofReal (√(Matrix.gram ℝ g).det) • Measure.map e volume := by
    rw [← hgram]; exact volume_eq_smul_map b
  have hFe : ∀ t, F (⟨Z, hZ⟩ + e t) =
      (∏ i, (Set.Ioi (0 : ℝ)).indicator (fun s : ℝ => Complex.exp (c i * s)) (t i)) * eLC l m Z := fun t => by
    have he : ((⟨Z, hZ⟩ + e t : V) : A0 k) = Z + ∑ j, t j • g j := congrArg (Z + ·) (hb t)
    by_cases ht : ∀ i, 0 < t i
    · rw [hF _ fun i => by rw [he, add_sub_cancel_left, key]; exact mul_pos (ht i) (h1 i), he,
        prod_congr rfl fun i _ => Set.indicator_of_mem (s := Set.Ioi 0) (ht i) _, ← Complex.exp_sum, eLC, eLC, ← Complex.exp_add]
      congr 1
      simp only [c, inner_add_right, inner_sum, real_inner_smul_right, sub_mul, sum_sub_distrib]
      push_cast
      simp only [mul_add, mul_sum]
      rw [sum_congr rfl fun i _ => mul_assoc Complex.I _ (t i : ℂ)]
      simp only [mul_comm (t _ : ℂ)]
      ring
    · rw [hF' _ fun h => ht fun i => by
        have := h i
        rw [he, add_sub_cancel_left, key] at this
        exact (mul_pos_iff_of_pos_right (h1 i)).1 this]
      obtain ⟨i, hi⟩ := not_forall.1 ht
      rw [prod_eq_zero (mem_univ i) (Set.indicator_of_notMem (show t i ∉ Set.Ioi (0 : ℝ) from hi) _), zero_mul]
  have I1 : Integrable fun H => F (⟨Z, hZ⟩ + H) := by
    rw [hv]
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_equiv]
    exact (i1.mul_const _).congr (.of_forall fun t => (hFe t).symm)
  refine ⟨by simpa using I1.comp_add_left (-⟨Z, hZ⟩), ?_⟩
  rw [← integral_add_left_eq_self F ⟨Z, hZ⟩, hv, integral_smul_measure, integral_map_equiv]
  simp only [hFe]
  rw [integral_mul_const, i2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Complex.real_smul, mul_assoc]

variable {k : ℕ}

theorem vec_mem {P : Finset (SV k)} {u : SV k} (hu : u ∈ P) : vec u ∈ aP P := Submodule.subset_span ⟨u, hu, rfl⟩

theorem pr_mem (P : Finset (SV k)) (x : A0 k) : pr P x ∈ aP P := Submodule.starProjection_apply_mem _ _

theorem sub_pr_inner {P : Finset (SV k)} (x : A0 k) {y : A0 k} (hy : y ∈ aP P) : ⟪x - pr P x, y⟫_ℝ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hy (Submodule.sub_starProjection_mem_orthogonal _)

theorem wt_inner {P : Finset (SV k)} (u : SV k) {y : A0 k} (hy : y ∈ aP P) : ⟪wt P u, y⟫_ℝ = 0 := sub_pr_inner _ hy

theorem wt_mem {P Q : Finset (SV k)} (e : Q ⊆ P) {u : SV k} (hu : u ∈ P) : wt Q u ∈ aP P :=
  sub_mem (vec_mem hu) (vecSpan_mono e (pr_mem _ _))

theorem mem_orth {P : Finset (SV k)} {x : A0 k} (h : ∀ q ∈ P, ⟪x, vec q⟫_ℝ = 0) : x ∈ (aP P)ᗮ := by
  refine (Submodule.mem_orthogonal' _ _).2 fun y hy => ?_
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨q, hq, rfl⟩ := hy; exact h q hq
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [real_inner_smul_right, hy, mul_zero]

theorem wt_inner_of_orth {Q : Finset (SV k)} (u : SV k) {x : A0 k} (hx : x ∈ (aP Q)ᗮ) :
    ⟪wt Q u, x⟫_ℝ = ⟪vec u, x⟫_ℝ := by
  rw [wt, inner_sub_left, Submodule.inner_right_of_mem_orthogonal (pr_mem _ _) hx, sub_zero]

theorem wt_orth (Q : Finset (SV k)) (u : SV k) : wt Q u ∈ (aP Q)ᗮ := mem_orth fun _ hq => wt_inner u (vec_mem hq)

theorem vec_inner_wt_pos {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) {u : SV k} (hu : u ∈ P \ Q) :
    0 < ⟪vec u, wt Q u⟫_ℝ := by
  rw [← wt_inner_of_orth u (wt_orth Q u)]
  exact real_inner_self_pos.2 (h.wt_ne_zero e hu)

theorem inner_vec_of_below {a b : SV k} (h : Below a b) :
    ⟪vec a, vec b⟫_ℝ = ⟪vec a, vec a⟫_ℝ ∧ ⟪vec a, vec a⟫_ℝ ≤ ⟪vec b, vec b⟫_ℝ := by
  simp only [vec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine ⟨sum_congr rfl fun i _ => ?_, sum_le_sum fun i _ => ?_⟩ <;> by_cases hi : a i = 0
  · simp [hi]
  · rw [h i hi]
  · simpa [hi] using mul_self_nonneg (b i : ℝ)
  · rw [h i hi]

theorem wt_inner_vec_nonneg {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) {u v : SV k} (hu : u ∈ P) (hv : v ∈ P) :
    0 ≤ ⟪wt Q u, vec v⟫_ℝ := by
  classical
  let n : SV k → ℝ := fun a => ⟪vec a, vec a⟫_ℝ
  have v0 : vec (0 : SV k) = 0 := by ext i; simp [vec]
  have n0 : ∀ a, n 0 ≤ n a := fun a => (inner_vec_of_below fun i hi => (hi rfl).elim).2
  have hmin : ∀ a ∈ insert 0 P, ∀ b ∈ P, ⟪vec a, vec b⟫_ℝ = min (n a) (n b) := fun a ha b hb => by
    have : Below a b ∨ Below b a := (mem_insert.1 ha).elim (fun e => .inl fun i hi => (hi (e ▸ rfl)).elim)
      fun ha => h.2 a ha b hb
    rcases this with e | e
    · rw [(inner_vec_of_below e).1, min_eq_left (inner_vec_of_below e).2]
    · rw [real_inner_comm, (inner_vec_of_below e).1, min_eq_right (inner_vec_of_below e).2]
  have hy : ∀ y ∈ aP Q, (∀ q ∈ Q, ⟪vec u - y, vec q⟫_ℝ = 0) → wt Q u = vec u - y := fun y hy h0 => by
    rw [wt, show pr Q (vec u) = y from Submodule.eq_starProjection_of_mem_orthogonal hy (mem_orth h0)]
  obtain ⟨a, ha, hA⟩ := exists_max_image ((insert 0 Q).filter (n · ≤ n u)) n ⟨0, by simp [n0]⟩
  obtain ⟨ha, hau⟩ := mem_filter.1 ha
  have ha' : vec a ∈ aP Q := (mem_insert.1 ha).elim (fun e => by rw [e, v0]; exact zero_mem _) vec_mem
  have haP := insert_subset_insert _ e ha
  have hA' : ∀ q ∈ Q, n q ≤ n u → n q ≤ n a := fun q hq hh => hA q (mem_filter.2 ⟨mem_insert_of_mem hq, hh⟩)
  have hu' := mem_insert_of_mem (b := 0) hu
  by_cases hB : (Q.filter (n u < n ·)).Nonempty
  · obtain ⟨b, hb, hB⟩ := exists_min_image _ n hB
    obtain ⟨hb, hub⟩ := mem_filter.1 hb
    have hD : 0 < n b - n a := by linarith
    have hc : ∀ w ∈ P, ⟪vec u - (((n b - n u) / (n b - n a)) • vec a + ((n u - n a) / (n b - n a)) • vec b), vec w⟫_ℝ =
        ((n b - n a) * min (n u) (n w) - (n b - n u) * min (n a) (n w) - (n u - n a) * min (n b) (n w)) / (n b - n a) :=
      fun w hw => by
        rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hmin u hu' w hw, hmin a haP w hw,
          hmin b (mem_insert_of_mem (e hb)) w hw]
        field_simp
        ring
    rw [hy _ (add_mem (Submodule.smul_mem _ _ ha') (Submodule.smul_mem _ _ (vec_mem hb))) fun q hq => ?_, hc v hv]
    · refine div_nonneg ?_ hD.le
      rcases le_total (n v) (n u) with h1 | h1
      · rw [min_eq_right h1, min_eq_right (h1.trans hub.le)]
        nlinarith [min_le_right (n a) (n v)]
      · rw [min_eq_left h1, min_eq_left (hau.trans h1)]
        nlinarith [min_le_left (n b) (n v)]
    · rw [hc q (e hq), div_eq_zero_iff]
      left
      rcases le_or_gt (n q) (n u) with h1 | h1
      · rw [min_eq_right h1, min_eq_right (h1.trans hub.le), min_eq_right (hA' q hq h1)]; ring
      · rw [min_eq_left h1.le, min_eq_left (hau.trans h1.le), min_eq_left (hB q (mem_filter.2 ⟨hq, h1⟩))]; ring
  · rw [hy _ ha' fun q hq => ?_, inner_sub_left, hmin u hu' v hv, hmin a haP v hv]
    · exact sub_nonneg.2 (min_le_min_right _ hau)
    · have h1 : n q ≤ n u := not_lt.1 fun h1 => hB ⟨q, mem_filter.2 ⟨hq, h1⟩⟩
      rw [inner_sub_left, hmin u hu' q (e hq), hmin a haP q (e hq), min_eq_right h1, min_eq_right (hA' q hq h1), sub_self]

theorem sum_vec_inner_wt_pos {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) {u : SV k} (hu : u ∈ P \ Q) :
    0 < ⟪∑ v ∈ P, vec v, wt Q u⟫_ℝ := by
  rw [sum_inner]
  exact sum_pos' (fun v hv => real_inner_comm (vec v) _ ▸ wt_inner_vec_nonneg h e (mem_sdiff.1 hu).1 hv)
    ⟨u, (mem_sdiff.1 hu).1, vec_inner_wt_pos h e hu⟩

theorem rt_inner {P : Finset (SV k)} (u : SV k) {y : A0 k} (hy : y ∈ aP (P.erase u)) : ⟪rt P u, y⟫_ℝ = 0 :=
  wt_inner u hy

theorem rt_mem {P : Finset (SV k)} {u : SV k} (hu : u ∈ P) : rt P u ∈ aP P := wt_mem (erase_subset _ _) hu

theorem rt_inner_wt_zero {P Q : Finset (SV k)} {u v : SV k} (hQ : Q ⊆ P.erase u) (hv : v ∈ P.erase u) :
    ⟪rt P u, wt Q v⟫_ℝ = 0 := rt_inner u (wt_mem hQ hv)

theorem rt_inner_wt_pos {P Q : Finset (SV k)} (h : IsPar P) {u : SV k} (hu : u ∈ P) (hQ : Q ⊆ P.erase u) :
    0 < ⟪rt P u, wt Q u⟫_ℝ := by
  rw [wt, inner_sub_right, rt_inner u (vecSpan_mono hQ (pr_mem _ _)), sub_zero, real_inner_comm]
  exact vec_inner_wt_pos h (erase_subset _ _) (by simp [hu])

theorem subset_erase {P S : Finset (SV k)} (hSP : S ⊆ P) {u : SV k} (hu : u ∈ P \ S) : S ⊆ P.erase u :=
  fun x hx => mem_erase.2 ⟨fun e => (mem_sdiff.1 hu).2 (by rw [← e]; exact hx), hSP hx⟩

theorem finrank_aP {P : Finset (SV k)} (h : IsPar P) : Module.finrank ℝ (aP P) = P.card := by
  have li : LinearIndepOn ℝ vec (P : Set (SV k)) := by
    rw [linearIndepOn_iff_notMem_span]
    intro u hu
    rw [show (P : Set (SV k)) \ {u} = ((P.erase u : Finset (SV k)) : Set (SV k)) by rw [Finset.coe_erase]]
    exact h.vec_notMem hu
  rw [aP, Set.image_eq_range]
  simpa using finrank_span_eq_card li

theorem finrank_aMQ {P R : Finset (SV k)} (h : IsPar P) (e : R ⊆ P) :
    Module.finrank ℝ (aMQ (aP P) R) + R.card = P.card := by
  have := Submodule.finrank_add_inf_finrank_orthogonal (vecSpan_mono e)
  rw [finrank_aP h, finrank_aP (h.mono e), inf_comm] at this
  rw [aMQ]; omega

def gen (P S R : Finset (SV k)) : ↥(P \ S) ⊕ ↥(S \ R) → A0 k := Sum.elim (fun u => wt S u) (fun u => rt S u)

def wall (P S R : Finset (SV k)) : ↥(P \ S) ⊕ ↥(S \ R) → A0 k := Sum.elim (fun u => rt P u) (fun u => wt R u)

variable {P S R : Finset (SV k)}

theorem orth_mono (e : R ⊆ S) : (aP S)ᗮ ≤ (aP R)ᗮ := Submodule.orthogonal_le (vecSpan_mono e)

theorem apex_mem (hRS : R ⊆ S) (Y : A0 k) : pr S Y - pr R Y ∈ aP S := sub_mem (pr_mem _ _) (vecSpan_mono hRS (pr_mem _ _))

theorem apex_mem_aMQ (hSP : S ⊆ P) (hRS : R ⊆ S) (Y : A0 k) : pr S Y - pr R Y ∈ aMQ (aP P) R :=
  ⟨vecSpan_mono hSP (apex_mem hRS Y), by
    rw [show pr S Y - pr R Y = (Y - pr R Y) - (Y - pr S Y) by abel]
    exact sub_mem (Submodule.sub_starProjection_mem_orthogonal _)
      (orth_mono hRS (Submodule.sub_starProjection_mem_orthogonal _))⟩

theorem gen_mem (hSP : S ⊆ P) (hRS : R ⊆ S) : ∀ i, gen P S R i ∈ aMQ (aP P) R := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩)
  · exact ⟨wt_mem hSP (mem_sdiff.1 hu).1, orth_mono hRS (wt_orth _ _)⟩
  · exact ⟨vecSpan_mono hSP (rt_mem (mem_sdiff.1 hu).1), orth_mono (subset_erase hRS hu) (wt_orth _ _)⟩

theorem card_gen (h : IsPar P) (hSP : S ⊆ P) (hRS : R ⊆ S) :
    Fintype.card (↥(P \ S) ⊕ ↥(S \ R)) = Module.finrank ℝ (aMQ (aP P) R) := by
  have a1 := finrank_aMQ h (hRS.trans hSP)
  have a2 := card_sdiff_add_card_eq_card hSP
  have a3 := card_sdiff_add_card_eq_card hRS
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
  omega

theorem wall_gen_zero (hSP : S ⊆ P) (hRS : R ⊆ S) : ∀ i j, i ≠ j → ⟪wall P S R i, gen P S R j⟫_ℝ = 0 := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩) (⟨v, hv⟩ | ⟨v, hv⟩) hij
  · exact rt_inner_wt_zero (subset_erase hSP hu)
      (mem_erase.2 ⟨fun (e : v = u) => hij (by subst e; rfl), (mem_sdiff.1 hv).1⟩)
  · exact rt_inner u (vecSpan_mono (subset_erase hSP hu) (rt_mem (mem_sdiff.1 hv).1))
  · exact (real_inner_comm _ _).trans (wt_inner v (wt_mem hRS (mem_sdiff.1 hu).1))
  · exact (real_inner_comm _ _).trans (rt_inner_wt_zero (subset_erase hRS hv)
      (mem_erase.2 ⟨fun (e : u = v) => hij (by subst e; rfl), (mem_sdiff.1 hu).1⟩))

theorem wall_gen_pos (h : IsPar P) (hSP : S ⊆ P) (hRS : R ⊆ S) : ∀ i, 0 < ⟪wall P S R i, gen P S R i⟫_ℝ := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩)
  · exact rt_inner_wt_pos h (mem_sdiff.1 hu).1 (subset_erase hSP hu)
  · exact (rt_inner_wt_pos (h.mono hSP) (mem_sdiff.1 hu).1 (subset_erase hRS hu)).trans_eq (real_inner_comm _ _)

theorem sum_vec_gen_pos (h : IsPar P) (hSP : S ⊆ P) : ∀ i, 0 < ⟪∑ v ∈ P, vec v, gen P S R i⟫_ℝ := by
  rintro (⟨u, hu⟩ | ⟨u, hu⟩)
  · exact sum_vec_inner_wt_pos h hSP hu
  · exact sum_vec_inner_wt_pos h ((erase_subset _ _).trans hSP) (mem_sdiff.2 ⟨hSP (mem_sdiff.1 hu).1, by simp⟩)

theorem wall_pos_iff (hSP : S ⊆ P) (hRS : R ⊆ S) (Y H : A0 k) :
    (∀ i, 0 < ⟪wall P S R i, H - (pr S Y - pr R Y)⟫_ℝ) ↔
      (∀ u ∈ P \ S, 0 < ⟪rt P u, H⟫_ℝ) ∧ ∀ u ∈ S \ R, 0 < ⟪wt R u, H - Y⟫_ℝ := by
  have e1 : ∀ u ∈ P \ S, ⟪rt P u, H - (pr S Y - pr R Y)⟫_ℝ = ⟪rt P u, H⟫_ℝ := fun u hu => by
    rw [inner_sub_right, rt_inner u (vecSpan_mono (subset_erase hSP hu) (apex_mem hRS Y)), sub_zero]
  have e2 : ∀ u ∈ S \ R, ⟪wt R u, H - (pr S Y - pr R Y)⟫_ℝ = ⟪wt R u, H - Y⟫_ℝ := fun u hu => by
    have a1 : ⟪wt R u, Y - pr S Y⟫_ℝ = 0 :=
      (real_inner_comm _ _).trans (sub_pr_inner Y (wt_mem hRS (mem_sdiff.1 hu).1))
    have a2 : ⟪wt R u, pr R Y⟫_ℝ = 0 := wt_inner u (pr_mem _ _)
    rw [inner_sub_right] at a1
    rw [inner_sub_right, inner_sub_right, inner_sub_right]
    linarith
  constructor
  · intro hh
    exact ⟨fun u hu => (hh (Sum.inl ⟨u, hu⟩)).trans_eq (e1 u hu), fun u hu => (hh (Sum.inr ⟨u, hu⟩)).trans_eq (e2 u hu)⟩
  · rintro ⟨a, b⟩ (⟨u, hu⟩ | ⟨u, hu⟩)
    · exact (a u hu).trans_eq (e1 u hu).symm
    · exact (b u hu).trans_eq (e2 u hu).symm

theorem det_gram_gen : (Matrix.gram ℝ (gen P S R)).det =
    (Matrix.gram ℝ fun u : ↥(P \ S) => wt S u).det * (Matrix.gram ℝ fun u : ↥(S \ R) => rt S u).det := by
  have hgram : Matrix.gram ℝ (gen P S R) = Matrix.fromBlocks (Matrix.gram ℝ fun u : ↥(P \ S) => wt S u) 0 0
      (Matrix.gram ℝ fun u : ↥(S \ R) => rt S u) := by
    ext (⟨u, hu⟩ | ⟨u, hu⟩) (⟨v, hv⟩ | ⟨v, hv⟩)
    · rfl
    · exact wt_inner u (rt_mem (mem_sdiff.1 hv).1)
    · exact (real_inner_comm _ _).trans (wt_inner v (rt_mem (mem_sdiff.1 hu).1))
    · rfl
  rw [hgram, Matrix.det_fromBlocks_zero₂₁]

theorem prod_gen (φ : A0 k → ℂ) : ∏ i, -φ (gen P S R i) =
    ((-1) ^ (P \ S).card * ∏ u ∈ P \ S, φ (wt S u)) * ((-1) ^ (S \ R).card * ∏ u ∈ S \ R, φ (rt S u)) := by
  rw [Fintype.prod_sum_type, ← prod_neg, ← prod_neg, ← Finset.prod_coe_sort (P \ S), ← Finset.prod_coe_sort (S \ R)]
  rfl

theorem term (h : IsPar P) (hSP : S ⊆ P) (hRS : R ⊆ S) (Y l m : A0 k) (hm : ∀ i, 0 < ⟪m, gen P S R i⟫_ℝ) :
    Integrable (fun H : aMQ (aP P) R => eLC l m H *
      (((-1) ^ (S \ R).card * tau P S H * tauHat S R (H - Y) : ℝ) : ℂ)) ∧
    ∫ H : aMQ (aP P) R, eLC l m H * (((-1) ^ (S \ R).card * tau P S H * tauHat S R (H - Y) : ℝ) : ℂ) =
      (-1) ^ (P \ S).card * epsOfC (P \ S) (wt S) l m * epsOfC (S \ R) (rt S) l m * eLC l m (pr S Y - pr R Y) := by
  obtain ⟨c1, c2⟩ := cone (aMQ (aP P) R) (wall P S R) (gen P S R) (pr S Y - pr R Y) l m (apex_mem_aMQ hSP hRS Y)
    (gen_mem hSP hRS) (card_gen h hSP hRS) (wall_gen_zero hSP hRS) (wall_gen_pos h hSP hRS) hm
    (fun H => eLC l m H * ((tau P S H * tauHat S R (H - Y) : ℝ) : ℂ))
    (fun H hH => by
      obtain ⟨a, b⟩ := (wall_pos_iff hSP hRS Y H).1 hH
      rw [tau, tauHat, if_pos a, if_pos b, mul_one, Complex.ofReal_one, mul_one])
    (fun H hH => by
      rcases not_and_or.1 (mt (wall_pos_iff hSP hRS Y H).2 hH) with a | a
      · rw [tau, if_neg a, zero_mul, Complex.ofReal_zero, mul_zero]
      · rw [tauHat, if_neg a, mul_zero, Complex.ofReal_zero, mul_zero])
  have hmul : ∀ H : A0 k, eLC l m H * (((-1) ^ (S \ R).card * tau P S H * tauHat S R (H - Y) : ℝ) : ℂ) =
      ((-1) ^ (S \ R).card : ℂ) * (eLC l m H * ((tau P S H * tauHat S R (H - Y) : ℝ) : ℂ)) := fun H => by
    push_cast; ring
  simp only [hmul]
  refine ⟨c1.const_mul _, ?_⟩
  rw [integral_const_mul, c2, det_gram_gen, Real.sqrt_mul (Matrix.posSemidef_gram ℝ _).det_nonneg,
    prod_gen fun x => (Complex.I * (⟪l, x⟫_ℝ : ℝ) - (⟪m, x⟫_ℝ : ℝ))⁻¹, Complex.ofReal_mul, epsOfC, epsOfC]
  have sq : ((-1 : ℂ) ^ (S \ R).card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  generalize ((-1 : ℂ) ^ (S \ R).card) = s at sq ⊢
  generalize ((√(Matrix.gram ℝ fun u : ↥(P \ S) => wt S u).det : ℝ) : ℂ) = a
  generalize ((√(Matrix.gram ℝ fun u : ↥(S \ R) => rt S u).det : ℝ) : ℂ) = b
  generalize (∏ u ∈ P \ S, (Complex.I * (⟪l, wt S u⟫_ℝ : ℝ) - (⟪m, wt S u⟫_ℝ : ℝ))⁻¹) = x
  generalize (∏ u ∈ S \ R, (Complex.I * (⟪l, rt S u⟫_ℝ : ℝ) - (⟪m, rt S u⟫_ℝ : ℝ))⁻¹) = y
  linear_combination ((-1 : ℂ) ^ (P \ S).card * a * b * x * y * eLC l m (pr S Y - pr R Y)) * sq

theorem damped (k : ℕ) (P R : Finset (SV k)) (Y : A0 k) (h : IsPar P) (_hR : R ⊆ P) : ∃ m : A0 k, ∀ t : ℝ, 0 < t →
    ∀ l : A0 k, Integrable (fun H : aMQ (aP P) R => eLC l (t • m) H * gamP P R Y H) ∧
    ∫ H : aMQ (aP P) R, eLC l (t • m) H * gamP P R Y H = ∑ S ∈ between P R, (-1) ^ (P \ S).card *
      epsOfC (P \ S) (wt S) l (t • m) * epsOfC (S \ R) (rt S) l (t • m) * eLC l (t • m) (pr S Y - pr R Y) := by
  refine ⟨∑ v ∈ P, vec v, fun t ht l => ?_⟩
  have hb : ∀ S ∈ between P R, S ⊆ P ∧ R ⊆ S := fun S hS => by simpa [between] using hS
  have T := fun S hS => term h (hb S hS).1 (hb S hS).2 Y l (t • ∑ v ∈ P, vec v) fun i => by
    rw [real_inner_smul_left]
    exact mul_pos ht (sum_vec_gen_pos h (hb S hS).1 i)
  simp only [gamP, Complex.ofReal_sum, mul_sum]
  refine ⟨integrable_finset_sum _ fun S hS => (T S hS).1, ?_⟩
  rw [integral_finset_sum _ fun S hS => (T S hS).1]
  exact sum_congr rfl fun S hS => (T S hS).2

end GlobalTheory.Chamber.DampedCone

end
