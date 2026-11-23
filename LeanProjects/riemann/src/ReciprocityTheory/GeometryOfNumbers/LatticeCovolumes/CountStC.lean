import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStB

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def gramR (h : HermFam K V) {r : ℕ} (v : Fin r → V)
    (w : {w : InfinitePlace K // w.IsReal}) : Matrix (Fin r) (Fin r) ℝ :=
  (h.gram w.1.embedding v).map Complex.re

def ellS (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    Set (Fin r → mixedEmbedding.mixedSpace K) :=
  {y | (∀ w, qR (gramR h v w) (fun i => (y i).1 w) ≤ R ^ 2) ∧
    ∀ w : {w : InfinitePlace K // w.IsComplex}, qC (h.gram w.1.embedding v) (fun i => (y i).2 w) ≤ R ^ 2}

theorem gram_posDef (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hli : LinearIndependent K v) : (h.gram σ v).PosDef := h.posDef σ r v hli

private lemma finsupp_sum_sum_star_mul_eq_qR {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (y : Fin r →₀ ℝ) :
    (y.sum fun i xi => y.sum fun j xj => star xi * M i j * xj) = qR M y := by
  unfold qR
  rw [Finsupp.sum_fintype]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype]
    · simp only [star_trivial]
    · intro j
      simp
  · intro i
    simp

private lemma finsupp_sum_sum_star_mul_re_eq_qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (z : Fin r →₀ ℂ) :
    (z.sum fun i xi => z.sum fun j xj => star xi * G i j * xj).re = qC G z := by
  unfold qC
  rw [Finsupp.sum_fintype]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype]
    · simp only [Complex.star_def]
    · intro j
      simp
  · intro i
    simp

private lemma qR_map_re_eq_qC_ofReal {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℝ) :
    qR (G.map Complex.re) y = qC G (fun i => (y i : ℂ)) := by
  unfold qR qC
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.re_ofReal_mul, Complex.re_mul_ofReal, Matrix.map_apply] <;> ring

theorem gramR_posDef (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (w : {w : InfinitePlace K // w.IsReal}) : (gramR h v w).PosDef := by
  have hG := gram_posDef h w.1.embedding hli
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun y hy => ?_⟩
  · simp only [gramR, Matrix.map_apply, star_trivial]
    rw [← hG.1.apply i j]
    simp [Complex.star_def]
  · have hz : Finsupp.mapRange (fun a : ℝ => (a : ℂ)) Complex.ofReal_zero y ≠ 0 := by
      intro h0
      apply hy
      ext i
      simpa using DFunLike.congr_fun h0 i
    have h1 := (Complex.lt_def.mp (hG.2 hz)).1
    rw [finsupp_sum_sum_star_mul_re_eq_qC] at h1
    have h2 : (⇑(Finsupp.mapRange (fun a : ℝ => (a : ℂ)) Complex.ofReal_zero y)) =
        fun i => (y i : ℂ) := by
      funext i
      simp
    rw [h2, ← qR_map_re_eq_qC_ofReal] at h1
    rw [finsupp_sum_sum_star_mul_eq_qR]
    simpa [gramR] using h1

private lemma form_sum_smul_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (a : ι → K) (u : ι → V) :
    h.form σ x (∑ i ∈ s, a i • u i) = ∑ i ∈ s, σ (a i) * h.form σ x (u i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using h.smul_right σ 0 x 0
  · intro j t hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, h.add_right, h.smul_right, ih]

private lemma form_sum_smul_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (a : ι → K) (u : ι → V) :
    h.form σ (∑ i ∈ s, a i • u i) y = ∑ i ∈ s, starRingEnd ℂ (σ (a i)) * h.form σ (u i) y := by
  rw [← h.conj_symm σ y, form_sum_smul_right h σ y s a u, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm]

theorem form_eq_qC (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} {v : Fin r → V}
    (hli : LinearIndependent K v) {x : V} (hx : x ∈ Submodule.span K (Set.range v)) :
    (h.form σ x x).re = qC (h.gram σ v) (fun i => σ (crd hli x i)) := by
  unfold qC HermFam.gram
  conv_lhs => rw [← sum_crd hli hx]
  rw [form_sum_smul_left]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

theorem qR_crdEmb (h : HermFam K V) {r : ℕ} {v : Fin r → V}
    (hli : LinearIndependent K v) {x : V} (hx : x ∈ Submodule.span K (Set.range v))
    (w : {w : InfinitePlace K // w.IsReal}) :
    qR (gramR h v w) (fun i => (crdEmb hli x i).1 w) = (h.form w.1.embedding x x).re := by
  rw [form_eq_qC h w.1.embedding hli hx, gramR, qR_map_re_eq_qC_ofReal]
  congr 1
  funext i
  show ((InfinitePlace.embedding_of_isReal w.2 (crd hli x i) : ℝ) : ℂ) = _
  exact InfinitePlace.embedding_of_isReal_apply w.2 _

theorem qC_crdEmb (h : HermFam K V) {r : ℕ} {v : Fin r → V}
    (hli : LinearIndependent K v) {x : V} (hx : x ∈ Submodule.span K (Set.range v))
    (w : {w : InfinitePlace K // w.IsComplex}) :
    qC (h.gram w.1.embedding v) (fun i => (crdEmb hli x i).2 w) = (h.form w.1.embedding x x).re := by
  exact (form_eq_qC h w.1.embedding hli hx).symm

def psi (K : Type*) [Field K] [NumberField K] (r : ℕ) (y : Fin r → mixedEmbedding.mixedSpace K) :
    ({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) × ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ) :=
  (fun w i => (y i).1 w, fun w i => (y i).2 w)

private lemma measurePreserving_pi_pi_swap {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → X) (j : κ) (i : ι) => f i j)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  classical
  have h1 : MeasurePreserving (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
    have hm : Measurable (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2) :=
      measurable_pi_lambda _ fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
    refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have he : (fun (f : ι → κ → X) (p : ι × κ) => f p.1 p.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H i j => H (i, j), fun H p => H p.1 p.2⟩
    rw [he, Measure.pi_pi, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => by rw [Measure.pi_pi]
  let e : (κ → ι → X) ≃ᵐ (ι × κ → X) :=
    { toFun := fun g p => g p.2 p.1
      invFun := fun g j i => g (i, j)
      left_inv := fun g => rfl
      right_inv := fun g => rfl
      measurable_toFun :=
        measurable_pi_lambda _ fun p => (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)
      measurable_invFun :=
        measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => measurable_pi_apply (i, j) }
  have h2 : MeasurePreserving e (Measure.pi fun _ => Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ) := by
    refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [e.map_apply]
    have he : e ⁻¹' Set.univ.pi s = Set.univ.pi fun j => Set.univ.pi fun i => s (i, j) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      exact ⟨fun H j i => H (i, j), fun H p => H p.2 p.1⟩
    rw [he, Measure.pi_pi, Fintype.prod_prod_type, Finset.prod_comm]
    exact Finset.prod_congr rfl fun j _ => by rw [Measure.pi_pi]
  exact (h2.symm e).comp h1

theorem measurePreserving_psi (r : ℕ) :
    MeasurePreserving (psi K r) volume
      ((Measure.pi fun _ => Measure.pi fun _ => volume).prod
        (Measure.pi fun _ => Measure.pi fun _ => volume)) := by
  have hA := measurePreserving_arrowProdEquivProdArrow ({w : InfinitePlace K // w.IsReal} → ℝ)
    ({w : InfinitePlace K // w.IsComplex} → ℂ) (Fin r) (fun _ => volume) (fun _ => volume)
  exact ((measurePreserving_pi_pi_swap (ι := Fin r) (κ := {w : InfinitePlace K // w.IsReal})
    (volume : Measure ℝ)).prod (measurePreserving_pi_pi_swap (ι := Fin r) (κ := {w : InfinitePlace K // w.IsComplex})
    (volume : Measure ℂ))).comp hA

theorem ellS_eq (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    ellS h v R = psi K r ⁻¹' ((Set.pi univ fun w => {u | qR (gramR h v w) u ≤ R ^ 2}) ×ˢ
      (Set.pi univ fun w : {w : InfinitePlace K // w.IsComplex} =>
        {u | qC (h.gram w.1.embedding v) u ≤ R ^ 2})) := by
  ext y
  simp [ellS, psi, Set.mem_pi]

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

def ellT (h : HermFam K V) {r : ℕ} (v : Fin r → V) (R : ℝ) :
    Set (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
      ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) :=
  (Set.pi univ fun w => {u | qR (gramR h v w) u ≤ R ^ 2}) ×ˢ
    (Set.pi univ fun w : {w : InfinitePlace K // w.IsComplex} =>
      {u | qC (h.gram w.1.embedding v) u ≤ R ^ 2})

theorem ellT_props (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : Convex ℝ (ellT h v R) ∧ Bornology.IsBounded (ellT h v R) ∧
      MeasurableSet (ellT h v R) := by
  have hR := fun w => ellipsoidR_props (gramR_posDef h hli w) R
  have hC := fun w : {w : InfinitePlace K // w.IsComplex} =>
    ellipsoidC_props (gram_posDef h w.1.embedding hli) R
  refine ⟨?_, ?_, ?_⟩
  · exact (convex_pi fun w _ => (hR w).1).prod (convex_pi fun w _ => (hC w).1)
  · exact (Bornology.IsBounded.pi fun w => (hR w).2.2.1).prod
      (Bornology.IsBounded.pi fun w => (hC w).2.2.1)
  · exact (MeasurableSet.univ_pi fun w => (hR w).2.2.2).prod
      (MeasurableSet.univ_pi fun w => (hC w).2.2.2)

def psiL (K : Type*) [Field K] [NumberField K] (r : ℕ) :
    (Fin r → mixedEmbedding.mixedSpace K) →ₗ[ℝ]
      (({w : InfinitePlace K // w.IsReal} → Fin r → ℝ) ×
        ({w : InfinitePlace K // w.IsComplex} → Fin r → ℂ)) where
  toFun := psi K r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_le_norm_psi {r : ℕ} (y : Fin r → mixedEmbedding.mixedSpace K) :
    ‖y‖ ≤ ‖psi K r y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
    calc ‖(y i).1 w‖ = ‖(psi K r y).1 w i‖ := rfl
      _ ≤ ‖(psi K r y).1 w‖ := norm_le_pi_norm _ i
      _ ≤ ‖(psi K r y).1‖ := norm_le_pi_norm _ w
      _ ≤ ‖psi K r y‖ := norm_fst_le _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
    calc ‖(y i).2 w‖ = ‖(psi K r y).2 w i‖ := rfl
      _ ≤ ‖(psi K r y).2 w‖ := norm_le_pi_norm _ i
      _ ≤ ‖(psi K r y).2‖ := norm_le_pi_norm _ w
      _ ≤ ‖psi K r y‖ := norm_snd_le _

theorem ellS_props (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : Convex ℝ (ellS h v R) ∧ (∀ y ∈ ellS h v R, -y ∈ ellS h v R) ∧
      Bornology.IsBounded (ellS h v R) ∧ MeasurableSet (ellS h v R) := by
  obtain ⟨hcv, hbd, hms⟩ := ellT_props h hli R
  have he : ellS h v R = psi K r ⁻¹' ellT h v R := ellS_eq h v R
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hcv.linear_preimage (psiL K r)
  · intro y hy
    refine ⟨fun w => ?_, fun w => ?_⟩
    · exact (ellipsoidR_props (gramR_posDef h hli w) R).2.1 _ (hy.1 w)
    · exact (ellipsoidC_props (gram_posDef h w.1.embedding hli) R).2.1 _ (hy.2 w)
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    refine isBounded_iff_forall_norm_le.2 ⟨C, fun y hy => ?_⟩
    rw [he] at hy
    exact (norm_le_norm_psi y).trans (hC _ hy)
  · rw [he]
    exact hms.preimage (measurePreserving_psi (K := K) r).measurable

theorem volume_ellS (h : HermFam K V) {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (R : ℝ) : (volume (ellS h v R)).toReal =
      (∏ w, (volume {u : Fin r → ℝ | qR (gramR h v w) u ≤ R ^ 2}).toReal) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          (volume {u : Fin r → ℂ | qC (h.gram w.1.embedding v) u ≤ R ^ 2}).toReal := by
  rw [show ellS h v R = psi K r ⁻¹' ellT h v R from ellS_eq h v R,
    (measurePreserving_psi r).measure_preimage (ellT_props h hli R).2.2.nullMeasurableSet, ellT,
    Measure.prod_prod, Measure.pi_pi,
    Measure.pi_pi, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod]
  all_goals rfl

theorem le_volume_ellS (h : HermFam K V) {r : ℕ} (hr : 0 < r) {v : Fin r → V}
    (hli : LinearIndependent K v) {R : ℝ} (hR : 0 < R) :
    (∏ w, (2 * R / Real.sqrt r) ^ r / Real.sqrt (gramR h v w).det) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          (2 * R ^ 2 / r) ^ r / (h.gram w.1.embedding v).det.re ≤
      (volume (ellS h v R)).toReal := by
  rw [volume_ellS h hli R]
  have ha : ∀ w : {w : InfinitePlace K // w.IsReal},
      0 ≤ (2 * R / Real.sqrt r) ^ r / Real.sqrt (gramR h v w).det := fun w => by positivity
  have hb : ∀ w : {w : InfinitePlace K // w.IsComplex},
      0 ≤ (2 * R ^ 2 / r) ^ r / (h.gram w.1.embedding v).det.re := fun w => by
    have hd : 0 < (h.gram w.1.embedding v).det.re := by
      simpa using (Complex.lt_def.mp (gram_posDef h w.1.embedding hli).det_pos).1
    exact div_nonneg (by positivity) hd.le
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => ha w)
      (fun w _ => le_volume_ellipsoidR (gramR_posDef h hli w) hR)
  · exact Finset.prod_le_prod (fun w _ => hb w)
      (fun w _ => le_volume_ellipsoidC (gram_posDef h w.1.embedding hli) hR)
  · exact Finset.prod_nonneg fun w _ => hb w
  · exact Finset.prod_nonneg fun w _ => ENNReal.toReal_nonneg

end ReciprocityTheory.GeometryOfNumbersTheory
