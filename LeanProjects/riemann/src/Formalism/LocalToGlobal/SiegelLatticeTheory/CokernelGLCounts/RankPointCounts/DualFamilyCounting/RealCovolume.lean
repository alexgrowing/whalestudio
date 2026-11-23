import Mathlib

noncomputable section

open MeasureTheory
open scoped Matrix

namespace Formalism.L2.SG.Pf.RealCovolume

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def reCo : (ι → κ → ℂ) ≃ₗ[ℝ] (ι × κ × Fin 2 → ℝ) where
  toFun a p := if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im
  invFun x i c := ⟨x (i, c, 0), x (i, c, 1)⟩
  map_add' a b := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  map_smul' r a := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  left_inv a := by funext i c; apply Complex.ext <;> simp
  right_inv x := by
    funext p
    obtain ⟨i, c, t⟩ := p
    fin_cases t <;> simp

theorem reCo_apply (a : ι → κ → ℂ) (p : ι × κ × Fin 2) :
    reCo a p = if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im := rfl

def bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ) := (Pi.basisFun ℝ (ι × κ × Fin 2)).map reCo.symm

theorem bstd_repr (a : ι → κ → ℂ) (p : ι × κ × Fin 2) : (bstd : Module.Basis _ ℝ (ι → κ → ℂ)).repr a p = reCo a p := by
  first
  | rfl
  | simp [bstd]

def Qf (g : κ → ℝ) (a b : ι → κ → ℂ) : ℝ := ∑ i, ∑ c, (a i c * star (b i c)).re * g c

theorem Qf_eq (g : κ → ℝ) (a b : ι → κ → ℂ) :
    Qf g a b = ∑ p : ι × κ × Fin 2, reCo a p * reCo b p * g p.2.1 := by
  simp only [Qf, Fintype.sum_prod_type, Fin.sum_univ_two, reCo_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring

def boxC : Set ℂ := {z | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}

theorem volume_boxC : volume boxC = 1 := by
  have h : boxC = Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    first
    | exact Iff.rfl
    | simp [boxC, Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

omit [DecidableEq ι] [DecidableEq κ] in
theorem volume_box : volume (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC) = 1 := by
  simp [volume_pi_pi, volume_boxC]

omit [DecidableEq ι] [DecidableEq κ] in
theorem isAddHaar_vol : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := by
  first
  | infer_instance
  | exact Measure.pi.isAddHaarMeasure _

private theorem mem_fundamentalDomain_reindex_bstd_iff {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) (m : ι → κ → ℂ) :
    m ∈ ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) ↔
      ∀ p, reCo m p ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ZSpan.mem_fundamentalDomain]
  first
  | simp only [Module.Basis.repr_reindex_apply, Equiv.symm_symm, bstd_repr]
  | simp only [Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, bstd_repr]
  constructor
  · intro h p
    have := h (e.symm p)
    rwa [Equiv.apply_symm_apply] at this
  · intro h j
    exact h (e j)

theorem volume_fd_std {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) :
    volume (ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm)) = 1 := by
  have hset : ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC := by
    ext m
    rw [mem_fundamentalDomain_reindex_bstd_iff]
    constructor
    · intro h
      rw [Set.mem_pi]
      intro i _
      rw [Set.mem_pi]
      intro c _
      show (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1
      exact ⟨by simpa [reCo_apply] using h (i, c, 0), by simpa [reCo_apply] using h (i, c, 1)⟩
    · intro h p
      obtain ⟨i, c, t⟩ := p
      have hi := Set.mem_pi.1 h i (Set.mem_univ _)
      have hic' := Set.mem_pi.1 hi c (Set.mem_univ _)
      have hic : (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1 := hic'
      rw [reCo_apply]
      fin_cases t
      · simpa using hic.1
      · simpa using hic.2
  rw [hset, volume_box]

theorem covol_of_gram {N : ℕ} (w : Fin N → (ι → κ → ℂ)) (g : κ → ℝ) (hg : ∀ c, g c ≠ 0)
    (hN : Fintype.card (ι × κ × Fin 2) = N)
    (hdet : (Matrix.of fun i j => Qf g (w i) (w j)).det ≠ 0) :
    Countable (AddSubgroup.closure (Set.range w)) ∧
    (∃ F : Set (ι → κ → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) ∧
    ∀ F : Set (ι → κ → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal (√|(Matrix.of fun i j => Qf g (w i) (w j)).det| / ∏ i : ι, ∏ c : κ, |g c|) := by
  have hEqW : (Submodule.span ℤ (Set.range w)).toAddSubgroup = AddSubgroup.closure (Set.range w) := by
    refine le_antisymm ?_ ((AddSubgroup.closure_le _).2 Submodule.subset_span)
    intro x hx
    exact Submodule.span_induction (p := fun x _ => x ∈ AddSubgroup.closure (Set.range w))
      (fun y hy => AddSubgroup.subset_closure hy) (AddSubgroup.zero_mem _)
      (fun _ _ _ _ hx hy => AddSubgroup.add_mem _ hx hy) (fun a _ _ hx => AddSubgroup.zsmul_mem _ hx a) hx
  have hL : ∀ x : ι → κ → ℂ, x ∈ AddSubgroup.closure (Set.range w) ↔ ∃ c : Fin N → ℤ, ∑ i, c i • w i = x := by
    intro x
    rw [← hEqW, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun]
  have hcount : Countable (AddSubgroup.closure (Set.range w)) := by
    refine Function.Surjective.countable
      (f := fun c : Fin N → ℤ => (⟨∑ i, c i • w i, (hL _).2 ⟨c, rfl⟩⟩ : AddSubgroup.closure (Set.range w))) ?_
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hL x).1 hx
    exact ⟨c, rfl⟩
  obtain ⟨e⟩ : Nonempty (Fin N ≃ ι × κ × Fin 2) := ⟨(Fintype.equivFinOfCardEq hN).symm⟩
  obtain ⟨b0, hb0def⟩ : ∃ b0 : Module.Basis (Fin N) ℝ (ι → κ → ℂ),
      b0 = (bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm := ⟨_, rfl⟩
  have hb0 : ∀ v k, b0.repr v k = reCo v (e k) := by
    intro v k
    rw [hb0def]
    first
    | rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm, bstd_repr]
    | simp [bstd_repr]
  have hvol0 : volume (ZSpan.fundamentalDomain b0) = 1 := by
    rw [hb0def]
    exact volume_fd_std e
  have hGram : (Matrix.of fun i j => Qf g (w i) (w j)) =
      (b0.toMatrix w)ᵀ * Matrix.diagonal (fun k => g (e k).2.1) * b0.toMatrix w := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply,
      Module.Basis.toMatrix_apply, hb0, Qf_eq]
    rw [← e.sum_comp]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetG : (Matrix.of fun i j => Qf g (w i) (w j)).det =
      (b0.toMatrix w).det * (b0.toMatrix w).det * ∏ k, g (e k).2.1 := by
    rw [hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    ring
  have hprod : ∏ k, g (e k).2.1 = ∏ i : ι, ∏ c : κ, (g c * g c) :=
    (e.prod_comp (fun p => g p.2.1)).trans (by simp only [Fintype.prod_prod_type, Fin.prod_univ_two])
  set P : ℝ := ∏ i : ι, ∏ c : κ, |g c| with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => Finset.prod_pos fun c _ => abs_pos.mpr (hg c)
  have habs : |∏ k, g (e k).2.1| = P * P := by
    rw [hprod, hPdef]
    simp only [Finset.abs_prod, abs_mul, Finset.prod_mul_distrib]
  have hval : √|(Matrix.of fun i j => Qf g (w i) (w j)).det| / P = |(b0.toMatrix w).det| := by
    rw [hdetG, abs_mul, abs_mul, habs,
      show |(b0.toMatrix w).det| * |(b0.toMatrix w).det| * (P * P) = (|(b0.toMatrix w).det| * P) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg (abs_nonneg _) hP.le)]
    exact mul_div_cancel_right₀ _ hP.ne'
  have hdetM : (b0.toMatrix w).det ≠ 0 := by
    intro h
    apply hdet
    rw [hdetG, h]
    ring
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hMc : (b0.toMatrix w) *ᵥ c = 0 := by
      ext k
      have h1 := congrArg (fun v => b0.repr v k) hc
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
      simp only [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetM hMc) i
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (ι → κ → ℂ) := by
    first
    | exact (Module.finrank_eq_card_basis b0).symm
    | exact (FiniteDimensional.finrank_eq_card_basis b0).symm
  have hsp : Submodule.span ℝ (Set.range w) = ⊤ := by
    first
    | exact Submodule.eq_top_of_finrank_eq ((finrank_span_eq_card hli).trans hcard)
    | exact Submodule.eq_top_of_finrank_eq ((finrank_span_eq_card hli).trans (by simpa using hcard))
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin N) ℝ (ι → κ → ℂ), ⇑b = w :=
    ⟨Module.Basis.mk hli hsp.ge, by simp⟩
  have hEq : (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup = AddSubgroup.closure (Set.range w) := by
    rw [hb]
    exact hEqW
  refine ⟨hcount, ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun v => ?_⟩,
    fun F hFm hF => ?_⟩
  · rw [← hEq]
    obtain ⟨a, ha, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
    refine ⟨⟨a.1, a.2⟩, ha, fun a' ha' => ?_⟩
    exact Subtype.ext (congrArg Subtype.val (huniq ⟨a'.1, a'.2⟩ ha'))
  · haveI := hcount
    haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := isAddHaar_vol
    have h1 : IsAddFundamentalDomain (AddSubgroup.closure (Set.range w)) F volume := by
      first
      | exact IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
      | exact IsAddFundamentalDomain.mk' hFm.nullMeasurableSet (by simpa only [AddSubgroup.vadd_def, vadd_eq_add] using hF)
    have h2 : IsAddFundamentalDomain (AddSubgroup.closure (Set.range w)) (ZSpan.fundamentalDomain b) volume := by
      rw [← hEq]
      exact ZSpan.isAddFundamentalDomain b volume
    rw [h1.measure_eq h2, ZSpan.measure_fundamentalDomain b volume b0, hvol0, mul_one, hval,
      Module.Basis.det_apply, hb]

end Formalism.L2.SG.Pf.RealCovolume
