import Mathlib

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PositivityTheory.KB.LocalOverlapAverage.SimpM

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def Sx (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

def bary {q : ℕ} (t : Fin q → ℝ) : Fin (q + 1) → ℝ := Fin.cons (1 - ∑ j, t j) t

lemma bary_sum {q : ℕ} (t : Fin q → ℝ) : ∑ j, bary t j = 1 := by
  simp [bary, Fin.sum_univ_succ]

lemma bary_nonneg {q : ℕ} {t : Fin q → ℝ} (ht : t ∈ Sx q) (j : Fin (q + 1)) : 0 ≤ bary t j := by
  obtain ⟨h1, h2⟩ := ht
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [bary, Fin.cons_zero]
    linarith
  · simp only [bary, Fin.cons_succ]
    exact h1 i

lemma pt_eq {q : ℕ} (t : Fin q → ℝ) (y : Fin (q + 1) → V) :
    y 0 + ∑ j, t j • (y j.succ - y 0) = ∑ j, bary t j • y j := by
  rw [Fin.sum_univ_succ]
  simp only [bary, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul, ← Finset.sum_smul]
  abel

def KS {q : ℕ} (A : Fin (q + 1) → V →L[ℝ] V) (B : Set V) : Set V :=
  {p | ∃ τ : Fin (q + 1) → ℝ, (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1 ∧
    ∃ y : Fin (q + 1) → V, (∀ j, y j ∈ B) ∧ p = ∑ j, τ j • A j (y j)}

lemma mem_KS {q : ℕ} (A : Fin (q + 1) → V →L[ℝ] V) (B : Set V) {t : Fin q → ℝ} (ht : t ∈ Sx q)
    {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ B) :
    A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)) ∈ KS A B :=
  ⟨bary t, bary_nonneg ht, bary_sum t, y, hy, pt_eq t (fun j => A j (y j))⟩

lemma isCompact_KS {q : ℕ} (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B) :
    IsCompact (KS A B) := by
  have hSc : IsClosed {τ : Fin (q + 1) → ℝ | (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1} := by
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_eq (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const)
  have hS : IsCompact {τ : Fin (q + 1) → ℝ | (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1} := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ : Fin (q + 1) => isCompact_Icc (a := (0:ℝ)) (b := 1)) hSc ?_
    intro τ hτ j _
    refine ⟨hτ.1 j, ?_⟩
    calc τ j ≤ ∑ i, τ i := Finset.single_le_sum (fun i _ => hτ.1 i) (Finset.mem_univ j)
      _ = 1 := hτ.2
  have hK : KS A B = (fun p : (Fin (q + 1) → ℝ) × (Fin (q + 1) → V) => ∑ j, p.1 j • A j (p.2 j)) ''
      ({τ : Fin (q + 1) → ℝ | (∀ j, 0 ≤ τ j) ∧ ∑ j, τ j = 1} ×ˢ Set.univ.pi fun _ => B) := by
    ext p
    constructor
    · rintro ⟨τ, h0, h1, y, hy, rfl⟩
      exact ⟨(τ, y), ⟨⟨h0, h1⟩, fun j _ => hy j⟩, rfl⟩
    · rintro ⟨⟨τ, y⟩, ⟨⟨h0, h1⟩, hy⟩, rfl⟩
      exact ⟨τ, h0, h1, y, fun j => hy j (Set.mem_univ j), rfl⟩
  rw [hK]
  refine (hS.prod (isCompact_univ_pi fun _ => hB)).image ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply j).comp continuous_fst).smul
    ((A j).continuous.comp ((continuous_apply j).comp continuous_snd))

lemma isClosed_Sx (q : ℕ) : IsClosed (Sx q) := by
  have h1 : IsClosed {t : Fin q → ℝ | ∀ j, 0 ≤ t j} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  have h2 : IsClosed {t : Fin q → ℝ | ∑ j, t j ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
  simp only [Sx, Set.setOf_and]
  exact h1.inter h2

lemma isCompact_Sx (q : ℕ) : IsCompact (Sx q) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset (isClosed_Sx q) ?_
  intro t ht j _
  exact ⟨ht.1 j, le_trans (Finset.single_le_sum (fun i _ => ht.1 i) (Finset.mem_univ j)) ht.2⟩

lemma vol_Sx (q : ℕ) : volume (Sx q) < ⊤ := (isCompact_Sx q).measure_lt_top

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma lint_affine (μ : Measure V) [μ.IsAddHaarMeasure] (T : V →ₗ[ℝ] V) (hT : LinearMap.det T ≠ 0) (c : V)
    {G : V → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (T x + c) ∂μ = ENNReal.ofReal |(LinearMap.det T)⁻¹| * ∫⁻ x, G x ∂μ := by
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hT
  have h1 : ∫⁻ x, G (T x + c) ∂μ = ∫⁻ x, G (x + c) ∂(Measure.map T μ) :=
    (lintegral_map (f := fun x => G (x + c)) (hG.comp (measurable_add_const c)) hTc.measurable).symm
  rw [h1, hmap, lintegral_smul_measure, lintegral_add_right_eq_self (fun x => G x) c, smul_eq_mul]

def nm (μ : Measure V) (B : Set V) : Measure V := (μ B)⁻¹ • μ.restrict B

def iS {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (y : Fin (q + 1) → V) : ℝ :=
  ∫ t in Sx q, ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0

lemma nm_prob (μ : Measure V) (B : Set V) (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) : IsProbabilityMeasure (nm μ B) :=
  ⟨by simp [nm, Measure.smul_apply, ENNReal.inv_mul_cancel h0 ht]⟩

lemma nm_fin (μ : Measure V) (B : Set V) (ht : μ B ≠ ⊤) : IsFiniteMeasure (nm μ B) := by
  constructor
  simp only [nm, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  by_cases h0 : μ B = 0
  · simp [h0]
  · rw [ENNReal.inv_mul_cancel h0 ht]
    exact ENNReal.one_lt_top

lemma ae_mem_pi (μ : Measure V) {B : Set V} (hB : MeasurableSet B) (hBt : μ B ≠ ⊤) (q : ℕ) :
    ∀ᵐ y ∂(Measure.pi fun _ : Fin (q + 1) => nm μ B), y ∈ Set.univ.pi fun _ => B := by
  haveI := nm_fin μ B hBt
  have h : ∀ᵐ x ∂(nm μ B), x ∈ B := Measure.ae_smul_measure (ae_restrict_mem hB) _
  simp only [Set.mem_univ_pi]
  exact ae_all_iff.2 fun i => Measure.tendsto_eval_ae_ae.eventually h

lemma cont_iS {q : ℕ} (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B)
    (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ContinuousOn ω (KS A B)) :
    ContinuousOn (fun y : Fin (q + 1) → V => iS ω fun j => A j (y j)) (Set.univ.pi fun _ => B) ∧
      ∃ M : ℝ, ∀ y ∈ Set.univ.pi (fun _ : Fin (q + 1) => B), |iS ω fun j => A j (y j)| ≤ M := by
  have hKc : IsCompact (Sx q ×ˢ Set.univ.pi (fun _ : Fin (q + 1) => B)) :=
    (isCompact_Sx q).prod (isCompact_univ_pi fun _ => hB)
  have hP : Continuous (fun p : (Fin q → ℝ) × (Fin (q + 1) → V) =>
      A 0 (p.2 0) + ∑ j, p.1 j • (A j.succ (p.2 j.succ) - A 0 (p.2 0))) := by fun_prop
  have hD : Continuous (fun p : (Fin q → ℝ) × (Fin (q + 1) → V) =>
      fun j : Fin q => A j.succ (p.2 j.succ) - A 0 (p.2 0)) := by fun_prop
  have hmaps : Set.MapsTo (fun p : (Fin q → ℝ) × (Fin (q + 1) → V) =>
      A 0 (p.2 0) + ∑ j, p.1 j • (A j.succ (p.2 j.succ) - A 0 (p.2 0)))
      (Sx q ×ˢ Set.univ.pi (fun _ : Fin (q + 1) => B)) (KS A B) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact mem_KS A B ht fun j => hy j (Set.mem_univ j)
  have hg : ContinuousOn (fun p : (Fin q → ℝ) × (Fin (q + 1) → V) =>
      ω (A 0 (p.2 0) + ∑ j, p.1 j • (A j.succ (p.2 j.succ) - A 0 (p.2 0)))
        (fun j : Fin q => A j.succ (p.2 j.succ) - A 0 (p.2 0)))
      (Sx q ×ˢ Set.univ.pi (fun _ : Fin (q + 1) => B)) :=
    continuous_eval.comp_continuousOn ((hω.comp hP.continuousOn hmaps).prodMk hD.continuousOn)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg
  have hvol : volume (Sx q) < ⊤ := vol_Sx q
  have hms : MeasurableSet (Sx q) := (isClosed_Sx q).measurableSet
  simp only [iS]
  refine ⟨?_, M * volume.real (Sx q), ?_⟩
  · refine continuousOn_of_dominated (bound := fun _ => M)
      (F := fun (y : Fin (q + 1) → V) (t : Fin q → ℝ) =>
        ω (A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)))
        (fun j : Fin q => A j.succ (y j.succ) - A 0 (y 0))) ?_ ?_ ?_ ?_
    · intro y hy
      refine ContinuousOn.aestronglyMeasurable ?_ hms
      exact hg.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, hy⟩)
    · intro y hy
      refine (ae_restrict_iff' hms).2 (Filter.Eventually.of_forall fun t ht => ?_)
      exact hM (t, y) ⟨ht, hy⟩
    · exact integrableOn_const hvol.ne
    · refine (ae_restrict_iff' hms).2 (Filter.Eventually.of_forall fun t ht => ?_)
      exact hg.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨ht, hy⟩)
  · intro y hy
    have := norm_setIntegral_le_of_norm_le_const hvol (fun t ht => hM (t, y) ⟨ht, hy⟩)
    simpa [Real.norm_eq_abs] using this

lemma integ_iS {q : ℕ} (μ : Measure V) [IsFiniteMeasureOnCompacts μ] (A : Fin (q + 1) → V →L[ℝ] V) {B : Set V} (hB : IsCompact B)
    (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ContinuousOn ω (KS A B))
    (w : (Fin (q + 1) → V) → Fin (q + 1) → V) (hw : Continuous w)
    (hwB : ∀ y ∈ Set.univ.pi (fun _ : Fin (q + 1) => B), w y ∈ Set.univ.pi fun _ => B) :
    Integrable (fun y => iS ω fun j => A j (w y j)) (Measure.pi fun _ : Fin (q + 1) => nm μ B) := by
  have hBt : μ B ≠ ⊤ := hB.measure_lt_top.ne
  haveI := nm_fin μ B hBt
  obtain ⟨hc, M, hM⟩ := cont_iS A hB ω hω
  have hs : MeasurableSet (Set.univ.pi fun _ : Fin (q + 1) => B) :=
    MeasurableSet.univ_pi fun _ => hB.isClosed.measurableSet
  have hae := ae_mem_pi μ hB.isClosed.measurableSet hBt q
  have hc' : ContinuousOn (fun y => iS ω fun j => A j (w y j)) (Set.univ.pi fun _ => B) :=
    hc.comp hw.continuousOn hwB
  refine Integrable.mono' (integrable_const M) ?_ ?_
  · have := hc'.aestronglyMeasurable (μ := Measure.pi fun _ : Fin (q + 1) => nm μ B) hs
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  · filter_upwards [hae] with y hy
    simpa [Real.norm_eq_abs] using hM _ (hwB y hy)

lemma det_ne {q : ℕ} (A : Fin (q + 1) → V ≃L[ℝ] V) (i : Fin (q + 1)) :
    LinearMap.det ((A i : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0 :=
  (A i).toLinearEquiv.isUnit_det'.ne_zero

lemma coord_step {q : ℕ} (μ : Measure V) [μ.IsAddHaarMeasure] (A : Fin (q + 1) → V ≃L[ℝ] V) (B : Set V)
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) {G : V → ℝ≥0∞} (hG : Measurable G) (τ : Fin (q + 1) → ℝ)
    (i : Fin (q + 1)) (hi : 1 / ((q : ℝ) + 1) ≤ τ i) :
    ∫⁻ y, G (∑ j, τ j • A j (y j)) ∂(Measure.pi fun _ : Fin (q + 1) => nm μ B) ≤
      (μ B)⁻¹ * ENNReal.ofReal (((q : ℝ) + 1) ^ Module.finrank ℝ V *
        |(LinearMap.det ((A i : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹|) * ∫⁻ x, G x ∂μ := by
  haveI := nm_prob μ B h0 ht
  set ν := nm μ B with hν
  set Ai : V →ₗ[ℝ] V := ((A i : V →L[ℝ] V) : V →ₗ[ℝ] V) with hAi
  have hq : (0:ℝ) < (q:ℝ) + 1 := by positivity
  have hτpos : 0 < τ i := lt_of_lt_of_le (by positivity) hi
  set T : V →ₗ[ℝ] V := τ i • Ai with hT
  have hdetA : LinearMap.det Ai ≠ 0 := det_ne A i
  have hdetT : LinearMap.det T = τ i ^ Module.finrank ℝ V * LinearMap.det Ai := LinearMap.det_smul _ _
  have hdetT0 : LinearMap.det T ≠ 0 := by
    rw [hdetT]
    exact mul_ne_zero (pow_ne_zero _ hτpos.ne') hdetA
  have hcoef : ENNReal.ofReal |(LinearMap.det T)⁻¹| ≤
      ENNReal.ofReal (((q : ℝ) + 1) ^ Module.finrank ℝ V * |(LinearMap.det Ai)⁻¹|) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdetT, mul_inv, abs_mul, ← inv_pow, abs_pow, abs_inv, abs_of_pos hτpos]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply pow_le_pow_left₀ (inv_nonneg.2 hτpos.le)
    rw [inv_le_comm₀ hτpos hq]
    simpa [one_div] using hi
  set K : ℝ≥0∞ := (μ B)⁻¹ * ENNReal.ofReal (((q : ℝ) + 1) ^ Module.finrank ℝ V *
    |(LinearMap.det Ai)⁻¹|) * ∫⁻ x, G x ∂μ with hK
  have hFm : Measurable fun y : Fin (q + 1) → V => G (∑ j, τ j • A j (y j)) := by
    refine hG.comp (Continuous.measurable ?_)
    exact continuous_finset_sum _ fun j _ => continuous_const.smul ((A j).continuous.comp (continuous_apply j))
  have hinner : ∀ z : Fin q → V, ∫⁻ x, G (∑ j, τ j • A j (Fin.insertNth (α := fun _ => V) i x z j)) ∂ν ≤ K := by
    intro z
    have hrw : ∀ x : V, ∑ j, τ j • A j (Fin.insertNth (α := fun _ => V) i x z j) =
        T x + ∑ j, τ (i.succAbove j) • A (i.succAbove j) (z j) := by
      intro x
      rw [Fin.sum_univ_succAbove _ i]
      simp [hT, hAi, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    simp_rw [hrw]
    calc ∫⁻ x, G (T x + ∑ j, τ (i.succAbove j) • A (i.succAbove j) (z j)) ∂ν
        ≤ (μ B)⁻¹ * ∫⁻ x, G (T x + ∑ j, τ (i.succAbove j) • A (i.succAbove j) (z j)) ∂μ := by
          rw [hν, nm, lintegral_smul_measure, smul_eq_mul]
          gcongr
          exact Measure.restrict_le_self
      _ = (μ B)⁻¹ * (ENNReal.ofReal |(LinearMap.det T)⁻¹| * ∫⁻ x, G x ∂μ) := by
          rw [lint_affine μ T hdetT0 _ hG]
      _ ≤ K := by
          rw [hK, mul_assoc]
          gcongr
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => ν) i).symm
  rw [← hmp.lintegral_comp hFm]
  rw [lintegral_prod_symm (fun a : V × (Fin q → V) => G (∑ j, τ j • A j ((MeasurableEquiv.piFinSuccAbove (fun _ => V) i).symm a j)))
    ((hFm.comp (MeasurableEquiv.measurable _)).aemeasurable)]
  calc _ ≤ ∫⁻ z : Fin q → V, K ∂(Measure.pi fun _ : Fin q => ν) := by
        refine lintegral_mono fun z => ?_
        simpa [MeasurableEquiv.piFinSuccAbove_symm_apply] using hinner z
    _ = K := by simp

lemma pt_eqA {q : ℕ} (A : Fin (q + 1) → V ≃L[ℝ] V) (t : Fin q → ℝ) (y : Fin (q + 1) → V) :
    A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)) = ∑ j, bary t j • A j (y j) :=
  pt_eq t (fun j => A j (y j))

lemma exists_big {q : ℕ} (τ : Fin (q + 1) → ℝ) (hs : ∑ j, τ j = 1) : ∃ i, 1 / ((q : ℝ) + 1) ≤ τ i := by
  by_contra h
  push_neg at h
  have hlt : ∑ j, τ j < ∑ _j : Fin (q + 1), 1 / ((q : ℝ) + 1) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h j
  rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  have hq : ((q : ℝ) + 1) ≠ 0 := by positivity
  push_cast at hlt
  rw [mul_one_div_cancel hq] at hlt
  exact lt_irrefl _ hlt

private theorem exists_ne_zero_smul_mem_of_mem_span' (μ : Measure V) [μ.IsAddHaarMeasure] {q : ℕ} (A : Fin (q + 1) → V ≃L[ℝ] V) {B : Set V}
    (hB : IsCompact B) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ContinuousOn ω (KS (fun j => (A j : V →L[ℝ] V)) B))
    (b : Fin (q + 1) → Bool) (y₀ : V) (hy₀ : y₀ ∈ B) :
    Integrable (fun y : Fin (q + 1) → V => iS ω fun j => A j (if b j then y j else y₀))
      (Measure.pi fun _ => nm μ B) := by
  have hw : Continuous fun y : Fin (q + 1) → V => fun j => if b j then y j else y₀ := by
    refine continuous_pi fun j => ?_
    by_cases h : b j = true
    · simp only [h, if_true]
      exact continuous_apply j
    · simp only [h]
      exact continuous_const
  have hwB : ∀ y ∈ Set.univ.pi (fun _ : Fin (q + 1) => B),
      (fun j => if b j then y j else y₀) ∈ Set.univ.pi fun _ : Fin (q + 1) => B := by
    intro y hy j _
    by_cases h : b j = true
    · simp only [h, if_true]
      exact hy j (Set.mem_univ j)
    · simp only [h]
      exact hy₀
  exact integ_iS μ (fun j => (A j : V →L[ℝ] V)) hB ω hω _ hw hwB

private theorem main_lemma_2 {q : ℕ} (f : V [⋀^Fin q]→L[ℝ] ℝ) (m : Fin q → V) (K : ℝ) (hK0 : 0 ≤ K)
    (hm : ∏ j, ‖m j‖ ≤ K) : ‖f m‖ₑ ≤ ENNReal.ofReal K * (‖f‖₊ : ℝ≥0∞) := by
  have h1 : ‖f m‖ ≤ K * ‖f‖ :=
    calc ‖f m‖ ≤ ‖f‖ * ∏ j, ‖m j‖ := f.le_opNorm m
      _ ≤ ‖f‖ * K := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ = K * ‖f‖ := mul_comm _ _
  rw [← ofReal_norm_eq_enorm]
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hK0]
  congr 1
  rw [ofReal_norm_eq_enorm]
  rfl

theorem main (μ : Measure V) [μ.IsAddHaarMeasure] (q : ℕ) (A : Fin (q + 1) → V ≃L[ℝ] V) (B : Set V)
    (hB : IsCompact B) : ∃ C : ℝ, ∀ ω : V → V [⋀^Fin q]→L[ℝ] ℝ,
      ContinuousOn ω (KS (fun j => (A j : V →L[ℝ] V)) B) →
      (∀ (b : Fin (q + 1) → Bool) (y₀ : V), y₀ ∈ B →
        Integrable (fun y : Fin (q + 1) → V => iS ω fun j => A j (if b j then y j else y₀))
          (Measure.pi fun _ => nm μ B)) ∧
      ENNReal.ofReal (∫ y, |iS ω fun j => A j (y j)| ∂(Measure.pi fun _ => nm μ B)) ≤
        ENNReal.ofReal C * ∫⁻ p in KS (fun j => (A j : V →L[ℝ] V)) B, ‖ω p‖₊ ∂μ := by
  classical
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hBt : μ B ≠ ⊤ := hB.measure_lt_top.ne
  haveI := nm_fin μ B hBt
  obtain ⟨r, hr⟩ := hB.isBounded.exists_norm_le
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∑ j, ‖(A j : V →L[ℝ] V)‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ Finset.sum_nonneg fun j _ => norm_nonneg _
  have hr0 : 0 ≤ max r 0 := le_max_right _ _
  have hAx : ∀ j, ∀ x ∈ B, ‖A j x‖ ≤ a * max r 0 := by
    intro j x hx
    calc ‖A j x‖ = ‖(A j : V →L[ℝ] V) x‖ := rfl
      _ ≤ ‖(A j : V →L[ℝ] V)‖ * ‖x‖ := (A j : V →L[ℝ] V).le_opNorm x
      _ ≤ a * max r 0 := mul_le_mul (ha ▸ Finset.single_le_sum (f := fun i => ‖(A i : V →L[ℝ] V)‖)
            (fun i _ => norm_nonneg _) (Finset.mem_univ j))
          ((hr x hx).trans (le_max_left _ _)) (norm_nonneg _) ha0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * a * max r 0) ^ q := ⟨_, rfl⟩
  have hc0 : 0 ≤ 2 * a * max r 0 := mul_nonneg (mul_nonneg (by norm_num) ha0) hr0
  have hK0 : 0 ≤ K := hK ▸ pow_nonneg hc0 _
  have hprod : ∀ y ∈ Set.univ.pi (fun _ : Fin (q + 1) => B),
      ∏ j : Fin q, ‖A j.succ (y j.succ) - A 0 (y 0)‖ ≤ K := by
    intro y hy
    have hy' : ∀ j, y j ∈ B := fun j => hy j (Set.mem_univ j)
    calc ∏ j : Fin q, ‖A j.succ (y j.succ) - A 0 (y 0)‖ ≤ ∏ _j : Fin q, (2 * a * max r 0) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => by
            calc ‖A j.succ (y j.succ) - A 0 (y 0)‖ ≤ ‖A j.succ (y j.succ)‖ + ‖A 0 (y 0)‖ := norm_sub_le _ _
              _ ≤ a * max r 0 + a * max r 0 := add_le_add (hAx _ _ (hy' _)) (hAx _ _ (hy' _))
              _ = 2 * a * max r 0 := by ring
      _ = K := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hK]
  by_cases h0 : μ B = 0
  · refine ⟨0, fun ω hω => ⟨fun b y₀ hy₀ => exists_ne_zero_smul_mem_of_mem_span' μ A hB ω hω b y₀ hy₀, ?_⟩⟩
    have hnm : nm μ B = 0 := by simp [nm, Measure.restrict_eq_zero.2 h0]
    have hP : Measure.pi (fun _ : Fin (q + 1) => nm μ B) = 0 := by
      rw [hnm]
      refine Measure.measure_univ_eq_zero.1 ?_
      rw [Measure.pi_univ]
      exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
    rw [hP, integral_zero_measure]
    simp
  haveI := nm_prob μ B h0 hBt
  obtain ⟨S, hS⟩ : ∃ S : ℝ≥0∞, S = ∑ i, ENNReal.ofReal (((q : ℝ) + 1) ^ Module.finrank ℝ V *
      |(LinearMap.det ((A i : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹|) := ⟨_, rfl⟩
  have hSt : S ≠ ⊤ := hS ▸ ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  obtain ⟨Cε, hCε⟩ : ∃ C : ℝ≥0∞, C = ENNReal.ofReal K * ((μ B)⁻¹ * S) * volume (Sx q) := ⟨_, rfl⟩
  have hCt : Cε ≠ ⊤ := hCε ▸ ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h0) hSt)) (vol_Sx q).ne
  refine ⟨Cε.toReal, fun ω hω => ⟨fun b y₀ hy₀ => exists_ne_zero_smul_mem_of_mem_span' μ A hB ω hω b y₀ hy₀, ?_⟩⟩
  rw [ENNReal.ofReal_toReal hCt]
  obtain ⟨G, hGdef⟩ : ∃ G : V → ℝ≥0∞, G = (KS (fun j => (A j : V →L[ℝ] V)) B).indicator
      (fun p => (‖ω p‖₊ : ℝ≥0∞)) := ⟨_, rfl⟩
  have hKSm : MeasurableSet (KS (fun j => (A j : V →L[ℝ] V)) B) :=
    (isCompact_KS _ hB).isClosed.measurableSet
  have hGm : Measurable G := by
    rw [hGdef, ← Set.piecewise_eq_indicator]
    exact ContinuousOn.measurable_piecewise
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hω) continuousOn_const hKSm
  have hGint : ∫⁻ x, G x ∂μ = ∫⁻ p in KS (fun j => (A j : V →L[ℝ] V)) B, ‖ω p‖₊ ∂μ := by
    rw [hGdef]
    exact lintegral_indicator hKSm _
  have hpt : ∀ y ∈ Set.univ.pi (fun _ : Fin (q + 1) => B),
      ENNReal.ofReal |iS ω fun j => A j (y j)| ≤
        ∫⁻ t in Sx q, ENNReal.ofReal K * G (A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0))) := by
    intro y hy
    have hy' : ∀ j, y j ∈ B := fun j => hy j (Set.mem_univ j)
    rw [← Real.enorm_eq_ofReal_abs]
    simp only [iS]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine setLIntegral_mono ?_ ?_
    · exact measurable_const.mul (hGm.comp (continuous_const.add
        (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)).measurable)
    · intro t ht
      have hmem : A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)) ∈
          KS (fun j => (A j : V →L[ℝ] V)) B := mem_KS _ B ht hy'
      rw [hGdef, Set.indicator_of_mem hmem]
      exact main_lemma_2 _ _ K hK0 (hprod y hy)
  have h1 : ENNReal.ofReal (∫ y, |iS ω fun j => A j (y j)| ∂(Measure.pi fun _ => nm μ B)) ≤
      ∫⁻ y, ENNReal.ofReal |iS ω fun j => A j (y j)| ∂(Measure.pi fun _ => nm μ B) := by
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    ext y
    rw [Real.enorm_eq_ofReal_abs, abs_abs]
  have h2 := lintegral_mono_ae ((ae_mem_pi μ hBm hBt q).mono fun y hy => hpt y hy)
  have hmeas : Measurable (Function.uncurry fun (y : Fin (q + 1) → V) (t : Fin q → ℝ) =>
      ENNReal.ofReal K * G (A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)))) := by
    refine measurable_const.mul (hGm.comp ?_)
    fun_prop
  have h3 := lintegral_lintegral_swap (μ := Measure.pi fun _ : Fin (q + 1) => nm μ B)
    (ν := volume.restrict (Sx q)) hmeas.aemeasurable
  have h4 : ∀ t ∈ Sx q, ∫⁻ y, ENNReal.ofReal K * G (A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)))
      ∂(Measure.pi fun _ => nm μ B) ≤ ENNReal.ofReal K * ((μ B)⁻¹ * S * ∫⁻ x, G x ∂μ) := by
    intro t ht
    have hmt : Measurable fun y : Fin (q + 1) → V => A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)) := by
      fun_prop
    rw [lintegral_const_mul (ENNReal.ofReal K)
      (f := fun y : Fin (q + 1) → V => G (A 0 (y 0) + ∑ j, t j • (A j.succ (y j.succ) - A 0 (y 0)))) (hGm.comp hmt)]
    gcongr ENNReal.ofReal K * ?_
    simp_rw [pt_eqA A t]
    obtain ⟨i, hi⟩ := exists_big (bary t) (bary_sum t)
    refine (coord_step μ A B h0 hBt hGm (bary t) i hi).trans ?_
    gcongr (μ B)⁻¹ * ?_ * _
    rw [hS]
    exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (((q : ℝ) + 1) ^ Module.finrank ℝ V *
      |(LinearMap.det ((A i : V →L[ℝ] V) : V →ₗ[ℝ] V))⁻¹|)) (fun _ _ => zero_le) (Finset.mem_univ i)
  have h5 := (setLIntegral_mono' (isClosed_Sx q).measurableSet h4).trans
    (le_of_eq (setLIntegral_const (μ := volume) _ _))
  refine h1.trans (h2.trans ((le_of_eq h3).trans (h5.trans (le_of_eq ?_))))
  rw [hCε, ← hGint]
  ring

end PositivityTheory.KB.LocalOverlapAverage.SimpM
