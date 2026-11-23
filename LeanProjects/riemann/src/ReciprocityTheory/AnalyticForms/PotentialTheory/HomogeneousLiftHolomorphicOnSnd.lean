import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

open OnePoint

noncomputable section

section Alg

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem FinHolAtlas.HoloOn.mono' {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ}
    (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem FinHolAtlas.SmoothOn.mono' {A : FinHolAtlas e X} {U V : Set X} {f : X → ℝ}
    (h : A.SmoothOn U f) (hVU : V ⊆ U) : A.SmoothOn V f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem FinHolAtlas.HoloOn.add' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x + g x) :=
  fun j => (hf j).add (hg j)

theorem FinHolAtlas.HoloOn.sub' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x - g x) :=
  fun j => (hf j).sub (hg j)

theorem FinHolAtlas.HoloOn.mul' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)

theorem FinHolAtlas.SmoothOn.add' {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ}
    (hf : A.SmoothOn U f) (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x + g x) :=
  fun j => (hf j).add (hg j)

end Alg

namespace CompatibleChartOperations

theorem isCompatChart_trans_cle {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ)) :
    IsCompatChart A ((A.chart i).trans L.toHomeomorph.toOpenPartialHomeomorph) := by
  intro j
  constructor
  · intro x hx
    have hx' : x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart i).source := ⟨hx.1, hx.2.1⟩
    exact (L.toContinuousLinearMap.analyticAt _).comp (A.holo j i x hx')
  · intro x hx
    have hx' : L.symm x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source := ⟨hx.1.2, hx.2⟩
    exact (A.holo i j (L.symm x) hx').comp (L.symm.toContinuousLinearMap.analyticAt x)

theorem isCompatChart_restrOpen {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (i : Fin A.n) (s : Set X) (hs : IsOpen s) : IsCompatChart A ((A.chart i).restrOpen s hs) := by
  intro j
  constructor
  · exact (A.holo j i).mono (fun x hx => ⟨hx.1, hx.2.1⟩)
  · exact (A.holo i j).mono (fun x hx => ⟨hx.1.1, hx.2⟩)

def shearLE : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 0 - v 1, v 1]
  invFun v := ![v 0 + v 1, v 1]
  map_add' u v := by ext i; fin_cases i <;> simp [add_sub_add_comm]
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_sub]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

def shearCLE : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) := shearLE.toContinuousLinearEquiv

theorem shearCLE_apply_zero (v : Fin 2 → ℂ) : shearCLE v 0 = v 0 - v 1 := rfl

open scoped Classical in
theorem projLineChart1_symm_ite (t : Fin 1 → ℂ) :
    projectiveLineChartAtInfinity.symm t = if t 0 = 0 then ∞ else (((t 0)⁻¹ : ℂ) : OnePoint ℂ) := rfl

open scoped Classical in
theorem fsPot_U_ite (a : OnePoint ℂ) :
    fsPot.U a = if a = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source := rfl

open scoped Classical in
theorem fsPot_φ_ite (a p : OnePoint ℂ) : fsPot.φ a p = if a = ∞ then (1 / 2) * Real.log (1 + ‖crd1 p‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 p‖ ^ 2) := rfl

def homogeneousCoord (p : OnePoint ℂ) : ℂ × ℂ := p.elim (0, 1) (fun z => (1, z))

open scoped Classical in

def homogeneousLift (a p : OnePoint ℂ) : ℂ × ℂ := if a = ∞ then (crd1 p, 1) else (1, crd0 p)

def det2 (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

def nrm2 (u : ℂ × ℂ) : ℝ := Real.sqrt (‖u.1‖ ^ 2 + ‖u.2‖ ^ 2)

open scoped Classical in

def chartIndexAt (a : OnePoint ℂ) : Fin 2 := if a = ∞ then 1 else 0

def chartCoordAt (a p : OnePoint ℂ) : ℂ := (p1.chart (chartIndexAt a) p) 0

theorem homogeneousLift_eq_smul {a p : OnePoint ℂ} (h : p ∈ fsPot.U a) :
    ∃ c : ℂ, c ≠ 0 ∧ homogeneousLift a p = c • homogeneousCoord p := by
  rw [fsPot_U_ite] at h
  by_cases ha : a = ∞
  · rw [if_pos ha] at h
    induction p with
    | infty => exact ⟨1, one_ne_zero, by simp [homogeneousLift, ha, homogeneousCoord, crd1]⟩
    | coe z =>
      have hz : z ≠ 0 := fun hz => h (by rw [hz])
      refine ⟨z⁻¹, inv_ne_zero hz, ?_⟩
      simp [homogeneousLift, ha, homogeneousCoord, crd1, hz]
  · rw [if_neg ha] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨1, one_ne_zero, by simp [homogeneousLift, ha, homogeneousCoord, crd0]⟩

theorem homogeneousLift_eq_smul' {a a' p : OnePoint ℂ} (h : p ∈ fsPot.U a) (h' : p ∈ fsPot.U a') :
    ∃ c : ℂ, c ≠ 0 ∧ homogeneousLift a p = c • homogeneousLift a' p := by
  obtain ⟨c, hc, e1⟩ := homogeneousLift_eq_smul h
  obtain ⟨c', hc', e2⟩ := homogeneousLift_eq_smul h'
  refine ⟨c / c', div_ne_zero hc hc', ?_⟩
  rw [e1, e2, smul_smul, div_mul_cancel₀ _ hc']

theorem pairDet_smul (c d : ℂ) (u v : ℂ × ℂ) : det2 (c • u) (d • v) = c * d * det2 u v := by
  simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem pairNorm_smul (c : ℂ) (u : ℂ × ℂ) : nrm2 (c • u) = ‖c‖ * nrm2 u := by
  simp only [nrm2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, norm_mul, mul_pow]
  rw [← mul_add, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem pairNorm_homogeneousLift_pos (a p : OnePoint ℂ) : 0 < nrm2 (homogeneousLift a p) := by
  unfold nrm2 homogeneousLift
  apply Real.sqrt_pos.2
  split_ifs <;> simp only [norm_one, one_pow] <;> positivity

theorem fsPot_φ_eq (a p : OnePoint ℂ) : fsPot.φ a p = Real.log (nrm2 (homogeneousLift a p)) := by
  rw [fsPot_φ_ite]
  unfold nrm2 homogeneousLift
  split_ifs <;> simp only [norm_one, one_pow] <;> rw [Real.log_sqrt (by positivity)] <;> ring_nf

theorem pairDet_homogeneousCoord_eq_zero {p q : OnePoint ℂ} (h : det2 (homogeneousCoord p) (homogeneousCoord q) = 0) : p = q := by
  induction p with
  | infty =>
    induction q with
    | infty => rfl
    | coe w => simp [homogeneousCoord, det2] at h
  | coe z =>
    induction q with
    | infty => simp [homogeneousCoord, det2] at h
    | coe w =>
      simp [homogeneousCoord, det2, sub_eq_zero] at h
      rw [h]

theorem pairDet_homogeneousLift_eq_zero {a b p q : OnePoint ℂ} (hp : p ∈ fsPot.U a) (hq : q ∈ fsPot.U b)
    (h : det2 (homogeneousLift a p) (homogeneousLift b q) = 0) : p = q := by
  obtain ⟨c, hc, e1⟩ := homogeneousLift_eq_smul hp
  obtain ⟨d, hd, e2⟩ := homogeneousLift_eq_smul hq
  rw [e1, e2, pairDet_smul] at h
  exact pairDet_homogeneousCoord_eq_zero ((mul_eq_zero.1 h).resolve_left (mul_ne_zero hc hd))

theorem chart_chartIndexAt_infty {a : OnePoint ℂ} (ha : a = ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtInfinity := by
  rw [chartIndexAt, if_pos ha]
  rfl

theorem chart_chartIndexAt_fin {a : OnePoint ℂ} (ha : a ≠ ∞) : p1.chart (chartIndexAt a) = projectiveLineChartAtZero := by
  rw [chartIndexAt, if_neg ha]
  rfl

theorem chartIndexAt_source (a : OnePoint ℂ) : (p1.chart (chartIndexAt a)).source = fsPot.U a := by
  rw [fsPot_U_ite]
  by_cases ha : a = ∞
  · rw [chart_chartIndexAt_infty ha, if_pos ha]
  · rw [chart_chartIndexAt_fin ha, if_neg ha]

open scoped Classical in
theorem pairDet_homogeneousLift_same (a p q : OnePoint ℂ) :
    det2 (homogeneousLift a p) (homogeneousLift a q) = (if a = ∞ then 1 else -1) * (chartCoordAt a p - chartCoordAt a q) := by
  by_cases ha : a = ∞
  · simp only [det2, homogeneousLift, chartCoordAt, if_pos ha, chart_chartIndexAt_infty ha]
    show crd1 p * 1 - 1 * crd1 q = 1 * (crd1 p - crd1 q)
    ring
  · simp only [det2, homogeneousLift, chartCoordAt, if_neg ha, chart_chartIndexAt_fin ha]
    show 1 * crd0 q - crd0 p * 1 = -1 * (crd0 p - crd0 q)
    ring

theorem homogeneousLift_holomorphicOn_fst (a : OnePoint ℂ) : p1.HoloOn (fsPot.U a) (fun p => (homogeneousLift a p).1) := by
  by_cases ha : a = ∞
  · have e : (fun p => (homogeneousLift a p).1) = crd1 := by
      funext p
      simp [homogeneousLift, ha]
    rw [e, fsPot_U_ite, if_pos ha]
    unfold FinHolAtlas.HoloOn
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show AnalyticOnNhd ℂ (crd1 ∘ projectiveLineChartAtZero.symm) (projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' projectiveLineChartAtInfinity.source)
      intro w hw
      have hw0 : w 0 ≠ 0 := projLineChart0_symm_ne_zero.1 hw.2
      have e2 : (crd1 ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => (w 0)⁻¹ := by
        funext w
        rfl
      rw [e2]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w).inv hw0
    · show AnalyticOnNhd ℂ (crd1 ∘ projectiveLineChartAtInfinity.symm) (projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' projectiveLineChartAtInfinity.source)
      intro w _
      have e2 : (crd1 ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => w 0 := by
        funext w
        exact infiniteCoord_projLineChart1_symm w
      rw [e2]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w
  · have e : (fun p => (homogeneousLift a p).1) = fun _ => (1 : ℂ) := by
      funext p
      simp [homogeneousLift, ha]
    rw [e]
    exact fun j w _ => analyticAt_const

theorem homogeneousLift_holomorphicOn_snd (a : OnePoint ℂ) : p1.HoloOn (fsPot.U a) (fun p => (homogeneousLift a p).2) := by
  by_cases ha : a = ∞
  · have e : (fun p => (homogeneousLift a p).2) = fun _ => (1 : ℂ) := by
      funext p
      simp [homogeneousLift, ha]
    rw [e]
    exact fun j w _ => analyticAt_const
  · have e : (fun p => (homogeneousLift a p).2) = crd0 := by
      funext p
      simp [homogeneousLift, ha]
    rw [e, fsPot_U_ite, if_neg ha]
    unfold FinHolAtlas.HoloOn
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show AnalyticOnNhd ℂ (crd0 ∘ projectiveLineChartAtZero.symm) (projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' projectiveLineChartAtZero.source)
      intro w _
      have e2 : (crd0 ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => w 0 := by
        funext w
        rfl
      rw [e2]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w
    · show AnalyticOnNhd ℂ (crd0 ∘ projectiveLineChartAtInfinity.symm) (projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' projectiveLineChartAtZero.source)
      intro w hw
      have hw0 : w 0 ≠ 0 := projLineChart1_symm_mem_range.1 hw.2
      have e2 : (crd0 ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => (w 0)⁻¹ := by
        funext w
        exact finiteCoord_projLineChart1_symm w
      rw [e2]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w).inv hw0

theorem ratio_smul (u v : ℂ × ℂ) {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) :
    ‖det2 (c • u) (d • v)‖ / (nrm2 (c • u) * nrm2 (d • v)) = ‖det2 u v‖ / (nrm2 u * nrm2 v) := by
  rw [pairDet_smul, pairNorm_smul, pairNorm_smul, norm_mul, norm_mul]
  rw [show ‖c‖ * nrm2 u * (‖d‖ * nrm2 v) = (‖c‖ * ‖d‖) * (nrm2 u * nrm2 v) by ring,
    mul_div_mul_left _ _ (mul_ne_zero (norm_ne_zero_iff.2 hc) (norm_ne_zero_iff.2 hd))]

end CompatibleChartOperations

end

end ReciprocityTheory.AnForm.M
