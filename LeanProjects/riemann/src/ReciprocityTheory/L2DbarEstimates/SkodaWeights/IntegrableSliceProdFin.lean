import ReciprocityTheory.L2DbarEstimates.SkodaWeights.WeightedIntegralEqLintegral

namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace

noncomputable section

theorem norm_sum_mul_sq_le {p : ℕ} (g a : Fin p → ℂ) :
    ‖∑ i, g i * a i‖ ^ 2 ≤ vsq g * ∑ i, ‖a i‖ ^ 2 := by
  unfold vsq
  have h1 : ‖∑ i, g i * a i‖ ≤ ∑ i, ‖g i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖g i‖) (fun i => ‖a i‖)
  calc ‖∑ i, g i * a i‖ ^ 2 ≤ (∑ i, ‖g i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem pt_G {p : ℕ} (g a : Fin p → ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ‖∑ i, g i * a i‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) ≤
      ∑ i, ‖a i‖ ^ 2 * Real.exp (-c) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  rw [hexp, ← Finset.sum_mul]
  have hcs := norm_sum_mul_sq_le g a
  have h1 : ‖∑ i, g i * a i‖ ^ 2 / vsq g ≤ ∑ i, ‖a i‖ ^ 2 := by
    rw [div_le_iff₀ hN, mul_comm]
    exact hcs
  have he := Real.exp_pos (-c)
  calc ‖∑ i, g i * a i‖ ^ 2 * (Real.exp (-c) / vsq g)
      = (‖∑ i, g i * a i‖ ^ 2 / vsq g) * Real.exp (-c) := by ring
    _ ≤ (∑ i, ‖a i‖ ^ 2) * Real.exp (-c) := by gcongr

theorem pt_Gs {p : ℕ} (g : Fin p → ℂ) (w : ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ∑ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 * Real.exp (-c) =
      ‖w‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  have hterm : ∀ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 =
      ‖w‖ ^ 2 * ‖g i‖ ^ 2 / vsq g ^ 2 := by
    intro i
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    ring
  have hv : (∑ i, ‖g i‖ ^ 2) = vsq g := rfl
  have hN' : vsq g ≠ 0 := hN.ne'
  rw [hexp]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, hv]
  field_simp
  try ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

private theorem isLocalHomeomorph_fst_prod_fin (p : ℕ) : IsLocalHomeomorph (Prod.fst : M × Fin p → M) := by
  intro q
  have hso : IsOpen {r : M × Fin p | r.2 = q.2} :=
    (isOpen_discrete ({q.2} : Set (Fin p))).preimage continuous_snd
  refine ⟨OpenPartialHomeomorph.mk (PartialHomeomorph.mk
    (PartialEquiv.mk Prod.fst (fun x => (x, q.2)) {r | r.2 = q.2} Set.univ
      (fun _ _ => Set.mem_univ _) (fun _ _ => rfl) (fun r hr => Prod.ext rfl hr.symm)
      (fun _ _ => rfl))
    continuous_fst.continuousOn (Continuous.prodMk continuous_id continuous_const).continuousOn)
    hso isOpen_univ, rfl, rfl⟩

private theorem isLocalHomeomorph_comp_prod_fst (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    IsLocalHomeomorph (fun q : M × Fin p => z q.1) :=
  hz.comp (isLocalHomeomorph_fst_prod_fin p)

private theorem vol_prod_fin_prod_singleton (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (B : Set M)
    (hB : MeasurableSet B) (i : Fin p) :
    vol n (fun q : M × Fin p => z q.1) (B ×ˢ {i}) = vol n z B := by
  rw [vol_apply n _ (isLocalHomeomorph_comp_prod_fst z hz p) _ (hB.prod (measurableSet_singleton i)),
    vol_apply n z hz B hB]
  unfold volFun
  congr 1
  funext y
  have e : (B ×ˢ {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} =
      (fun x => (x, i)) '' (B ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage,
      Set.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, hy⟩, rfl, rfl⟩
    · rintro ⟨a, ⟨ha, hy⟩, rfl, rfl⟩
      exact ⟨⟨ha, rfl⟩, hy⟩
  have hinj : Function.Injective (fun x : M => (x, i)) := fun a b h => congrArg Prod.fst h
  rw [e, hinj.injOn.encard_image]

private theorem vol_prod_fin_apply_eq_sum_preimage (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (A : Set (M × Fin p)) (hA : MeasurableSet A) :
    vol n (fun q : M × Fin p => z q.1) A = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' A) := by
  have hA' : A = ⋃ i : Fin p, ((fun x => (x, i)) ⁻¹' A) ×ˢ {i} := by
    ext ⟨x, j⟩
    simp
  have hm : ∀ i : Fin p, MeasurableSet ((fun x : M => (x, i)) ⁻¹' A) := fun i =>
    measurable_prodMk_right hA
  conv_lhs => rw [hA']
  rw [measure_iUnion (fun i j hij => Set.disjoint_prod.2 (Or.inr (Set.disjoint_singleton.2 hij)))
    (fun i => (hm i).prod (measurableSet_singleton i)), tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => vol_prod_fin_prod_singleton z hz p _ (hm i) i

private theorem vol_prod_fin_eq_sum_map_prodMk (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i : Fin p, (vol n z).map (fun x => (x, i)) := by
  ext A hA
  rw [vol_prod_fin_apply_eq_sum_preimage z hz p A hA, Measure.coe_finset_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (Measure.map_apply measurable_prodMk_right hA).symm

private theorem map_prodMk_right_vol_le_vol_prod_fin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (i : Fin p) :
    (vol n z).map (fun x => (x, i)) ≤ vol n (fun q : M × Fin p => z q.1) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply measurable_prodMk_right hs, vol_prod_fin_apply_eq_sum_preimage z hz p s hs]
  exact Finset.single_le_sum (f := fun j => vol n z ((fun x => (x, j)) ⁻¹' s))
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem ae_slice_prodFin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    {P : M × Fin p → Prop} (hP : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q) (i : Fin p) :
    ∀ᵐ x ∂vol n z, P (x, i) := by
  exact ae_of_ae_map measurable_prodMk_right.aemeasurable (ae_mono (map_prodMk_right_vol_le_vol_prod_fin z hz p i) hP)

theorem ae_lift_prodFin (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (hP : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by
  rw [ae_iff] at hP ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hP
  refine measure_mono_null (t := N ×ˢ Set.univ) (fun q hq => ⟨hsub hq, Set.mem_univ _⟩) ?_
  rw [vol_prod_fin_apply_eq_sum_preimage z hz p _ (hNm.prod MeasurableSet.univ)]
  simp [Set.mk_preimage_prod_left, hN0]

theorem measurable_vsq {p : ℕ} {g : Fin p → M → ℂ} (hg : ∀ l, Measurable (g l)) :
    Measurable (fun x => vsq (gv g x)) := by
  simp only [vsq, gv]
  exact Finset.measurable_sum _ fun i _ => ((hg i).norm).pow_const 2

theorem wint_G_le (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (h : M × Fin p → ℂ) (hh : Measurable h) :
    wint n z (fun x => ∑ i, g i x * h (x, i)) (fun x => φ x + Real.log (vsq (gv g x))) ≤
      wint n (fun q : M × Fin p => z q.1) h (fun q => φ q.1) := by
  show ∫⁻ x, ENNReal.ofReal (‖∑ i, g i x * h (x, i)‖ ^ 2 *
      Real.exp (-(φ x + Real.log (vsq (gv g x))))) ∂vol n z ≤
    ∫⁻ q, ENNReal.ofReal (‖h q‖ ^ 2 * Real.exp (-φ q.1)) ∂vol n (fun q : M × Fin p => z q.1)
  have hFm : Measurable (fun q : M × Fin p => ENNReal.ofReal (‖h q‖ ^ 2 * Real.exp (-φ q.1))) :=
    ((hh.norm.pow_const 2).mul (hφ.comp measurable_fst).neg.exp).ennreal_ofReal
  rw [vol_prod_fin_eq_sum_map_prodMk z hz p, lintegral_finset_sum_measure,
    Finset.sum_congr rfl fun i _ => lintegral_map hFm measurable_prodMk_right,
    ← lintegral_finset_sum (f := fun i a => ENNReal.ofReal (‖h (a, i)‖ ^ 2 *
      Real.exp (-φ (a, i).1))) _ fun i _ => hFm.comp measurable_prodMk_right]
  refine lintegral_mono fun x => ?_
  beta_reduce
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  exact ENNReal.ofReal_le_ofReal (pt_G (gv g x) (fun i => h (x, i)) (φ x) (hN x))

theorem wint_Gs_eq (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (g : Fin p → M → ℂ)
    (hg : ∀ l, Measurable (g l)) (φ : M → ℝ) (hφ : Measurable φ) (hN : ∀ x, 0 < vsq (gv g x))
    (w : M → ℂ) (hw : Measurable w) :
    wint n (fun q : M × Fin p => z q.1)
        (fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ))
        (fun q => φ q.1) =
      wint n z w (fun x => φ x + Real.log (vsq (gv g x))) := by
  show ∫⁻ q, ENNReal.ofReal (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
      Real.exp (-φ q.1)) ∂vol n (fun q : M × Fin p => z q.1) =
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * Real.exp (-(φ x + Real.log (vsq (gv g x))))) ∂vol n z
  have hvs := measurable_vsq hg
  have hg2 : Measurable (fun q : M × Fin p => g q.2 q.1) := by
    have e : (fun q : M × Fin p => g q.2 q.1) = fun q => ∑ j, if q.2 = j then g j q.1 else 0 := by
      funext q
      simp
    rw [e]
    exact Finset.measurable_sum _ fun j _ => Measurable.ite
      ((measurableSet_singleton j).preimage measurable_snd) ((hg j).comp measurable_fst)
      measurable_const
  have hFm : Measurable (fun q : M × Fin p => ENNReal.ofReal
      (‖w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ q.1))) := by
    refine (((((hw.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp hg2)).div
      (Complex.continuous_ofReal.measurable.comp (hvs.comp measurable_fst))).norm.pow_const 2).mul
      (hφ.comp measurable_fst).neg.exp).ennreal_ofReal
  rw [vol_prod_fin_eq_sum_map_prodMk z hz p, lintegral_finset_sum_measure,
    Finset.sum_congr rfl fun i _ => lintegral_map hFm measurable_prodMk_right,
    ← lintegral_finset_sum (f := fun i a => ENNReal.ofReal
      (‖w (a, i).1 * (starRingEnd ℂ) (g (a, i).2 (a, i).1) / ((vsq (gv g (a, i).1) : ℝ) : ℂ)‖ ^ 2 *
        Real.exp (-φ (a, i).1))) _ fun i _ => hFm.comp measurable_prodMk_right]
  refine lintegral_congr fun x => ?_
  beta_reduce
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  congr 1
  exact pt_Gs (gv g x) (w x) (φ x) (hN x)

def opG {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (f : M × Fin p → ℂ) : M → ℂ :=
  fun x => ∑ i, g i x * f (x, i)

def opS {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (w : M → ℂ) : M × Fin p → ℂ :=
  fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)

def adjK {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (φ : M → ℝ) (w : M → ℂ) (f : M × Fin p → ℂ) :
    M × Fin p → ℂ :=
  fun q => (Real.exp (-φ q.1) : ℂ) * ((starRingEnd ℂ) (opS g w q) * f q)

end

end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
