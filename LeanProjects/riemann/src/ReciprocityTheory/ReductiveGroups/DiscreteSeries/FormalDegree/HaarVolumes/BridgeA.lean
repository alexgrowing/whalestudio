import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.IntegralGaussEOmPhiOmE

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

namespace PolarCoordinateComparison

variable {N : ℕ}

abbrev eN (N : ℕ) : Fin N ⊕ Fin 0 ≃ Fin N := Equiv.sumEmpty (Fin N) (Fin 0)

lemma Jpq_zero (N : ℕ) : Formalism.UG.Jpq N 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

lemma Jm_true (N : ℕ) : Jm (fun _ : Fin N => true) = 1 := by
  simp [Jm, Formalism.REAL.Jm]

lemma cT_eq {m : Type} [Fintype m] (M : Matrix m m ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]

def psi (N : ℕ) : GL (Fin N ⊕ Fin 0) ℂ ≃* (Matrix (Fin N) (Fin N) ℂ)ˣ :=
  Units.mapEquiv (reindexAlgEquiv ℂ ℂ (eN N)).toMulEquiv

lemma psi_val (N : ℕ) (u : GL (Fin N ⊕ Fin 0) ℂ) :
    ((psi N u : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ) = reindex (eN N) (eN N) u := by
  rfl

lemma psi_symm_val (N : ℕ) (u : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    (((psi N).symm u : GL (Fin N ⊕ Fin 0) ℂ) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) =
      reindex (eN N).symm (eN N).symm u := by
  rfl

lemma mem_upq_iff (N : ℕ) (u : GL (Fin N ⊕ Fin 0) ℂ) :
    u ∈ Formalism.UG.Upq N 0 ↔ (u : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ * u = 1 := by
  show Formalism.UG.cT (starRingEnd ℂ) (u : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) * Formalism.UG.Jpq N 0 * u =
    Formalism.UG.Jpq N 0 ↔ _
  rw [Jpq_zero, cT_eq, Matrix.mul_one]

lemma mem_un_iff (N : ℕ) (u : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    u ∈ UNgrp N ↔ (u : Matrix (Fin N) (Fin N) ℂ)ᴴ * u = 1 := by
  show (u : Matrix (Fin N) (Fin N) ℂ)ᴴ * Formalism.REAL.Jm (fun _ : Fin N => true) * u =
    Formalism.REAL.Jm (fun _ : Fin N => true) ↔ _
  rw [show Formalism.REAL.Jm (fun _ : Fin N => true) = 1 by simp [Formalism.REAL.Jm], Matrix.mul_one]

lemma reindex_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (A : Matrix m m ℂ) (h : Aᴴ * A = 1) : (reindex e e A)ᴴ * reindex e e A = 1 := by
  rw [Matrix.conjTranspose_reindex]
  have hm := (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul Aᴴ A
  rw [h, map_one] at hm
  exact hm.symm

def iso (N : ℕ) : Formalism.BasicNotions.UpqT N 0 ≃* UNgrp N where
  toFun g := ⟨psi N (g : Formalism.UG.Upq N 0).1, by
    rw [mem_un_iff, psi_val]
    exact reindex_unitary _ _ ((mem_upq_iff N _).1 (g : Formalism.UG.Upq N 0).2)⟩
  invFun k := (⟨(psi N).symm k.1, by
    rw [mem_upq_iff, psi_symm_val]
    exact reindex_unitary _ _ ((mem_un_iff N _).1 k.2)⟩ : Formalism.UG.Upq N 0)
  left_inv g := Subtype.ext ((psi N).symm_apply_apply _)
  right_inv k := Subtype.ext ((psi N).apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul (psi N) _ _)

lemma toM_iso (N : ℕ) (g : Formalism.BasicNotions.UpqT N 0) :
    toM (iso N g) = reindex (eN N) (eN N) (Formalism.BasicNotions.UpqT.mat g) := psi_val N _

lemma mat_iso_symm (N : ℕ) (k : UNgrp N) :
    Formalism.BasicNotions.UpqT.mat ((iso N).symm k) = reindex (eN N).symm (eN N).symm (toM k) := psi_symm_val N _

lemma continuous_mat (N : ℕ) : Continuous (fun g : Formalism.BasicNotions.UpqT N 0 => Formalism.BasicNotions.UpqT.mat g) :=
  Units.continuous_val.comp continuous_subtype_val

lemma continuous_iso (N : ℕ) : Continuous (iso N) := by
  have hpsi : Continuous fun u : GL (Fin N ⊕ Fin 0) ℂ => psi N u :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_reindex _ _, Units.continuous_coe_inv.matrix_reindex _ _⟩
  exact (hpsi.comp continuous_subtype_val).subtype_mk _

instance instBorelUpqT (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

instance instBorelLieU (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

instance instContMulUpqT (N : ℕ) : ContinuousMul (Formalism.BasicNotions.UpqT N 0) :=
  inferInstanceAs (ContinuousMul (Formalism.UG.Upq N 0))

lemma continuous_psi_symm (N : ℕ) : Continuous (fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => (psi N).symm u) := by
  have hv : (Units.val ∘ fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => (psi N).symm u) =
      fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ => reindex (eN N).symm (eN N).symm (u : Matrix (Fin N) (Fin N) ℂ) := by
    funext u
    exact psi_symm_val N u
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · rw [hv]
    exact Units.continuous_val.matrix_reindex _ _
  have hf : (fun u : (Matrix (Fin N) (Fin N) ℂ)ˣ =>
      ((((psi N).symm u)⁻¹ : GL (Fin N ⊕ Fin 0) ℂ) : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) =
      fun u => reindex (eN N).symm (eN N).symm (((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ)) : Matrix (Fin N) (Fin N) ℂ) := by
    funext u
    rw [← map_inv, psi_symm_val]
  rw [hf]
  exact Units.continuous_coe_inv.matrix_reindex _ _

lemma continuous_iso_symm (N : ℕ) : Continuous (iso N).symm :=
  ((continuous_psi_symm N).comp continuous_subtype_val).subtype_mk _

def homeo (N : ℕ) : Formalism.BasicNotions.UpqT N 0 ≃ₜ UNgrp N where
  toEquiv := (iso N).toEquiv
  continuous_toFun := continuous_iso N
  continuous_invFun := continuous_iso_symm N

lemma map_iso_apply (N : ℕ) (μ : Measure (Formalism.BasicNotions.UpqT N 0)) (T : Set (UNgrp N)) :
    μ.map (iso N) T = μ ((iso N) ⁻¹' T) :=
  (homeo N).toMeasurableEquiv.map_apply T

def coords {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : UCo N :=
  (fun a => (M a a).im, fun ab => M ab.1.1 ab.1.2)

lemma skMat_coords {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hM : Mᴴ = -M) : skMat (coords M) = M := by
  ext a b
  have hab := congrFun (congrFun hM a) b
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at hab
  simp only [skMat, coords]
  split_ifs with h1 h2 h3
  · subst h1
    have hre : (M a a).re = 0 := by
      have h4 := congrArg Complex.re hab
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h4
      linarith
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [hre]
      ring
    · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
  · rfl
  · rw [hab, neg_neg]
  · rcases lt_trichotomy a b with h | h | h
    · exact absurd h h3
    · exact absurd h h1
    · exact absurd h h2

lemma lie_skew {N : ℕ} (X : Formalism.BasicNotions.lieU N 0) :
    (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ = -(X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) := by
  have h' : (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)ᴴ * Formalism.UG.Jpq N 0 +
      Formalism.UG.Jpq N 0 * (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) = 0 := X.2
  rw [Jpq_zero, Matrix.mul_one, Matrix.one_mul] at h'
  exact eq_neg_of_add_eq_zero_left h'

lemma uToLie_coords {N : ℕ} (X : Formalism.BasicNotions.lieU N 0) :
    uToLie (coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) = X := by
  have hsk : (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))ᴴ =
      -reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ) := by
    rw [Matrix.conjTranspose_reindex, lie_skew X]
    try rfl
  apply Subtype.ext
  show uToLieMat (coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ))) = X
  simp only [uToLieMat]
  rw [skMat_coords _ hsk]
  ext i j
  simp

lemma reindex_exp {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (A : Matrix m m ℂ) : reindex e e (NormedSpace.exp A) = NormedSpace.exp (reindex e e A) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A

lemma toM_preimage_exp_ball_eq_upqT_exp_ball (N : ℕ) (r : ℝ) :
    (iso N) ⁻¹' {k : UNgrp N | ∃ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, toM k = NormedSpace.exp (skMat x)} =
      {g | ∃ X ∈ Formalism.BasicNotions.ballU N 0 r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, toM_iso]
  constructor
  · rintro ⟨x, hx, hxe⟩
    refine ⟨uToLie x, hx, ?_⟩
    have hm : Formalism.BasicNotions.UpqT.mat g = reindex (eN N).symm (eN N).symm
        (reindex (eN N) (eN N) (Formalism.BasicNotions.UpqT.mat g)) := by
      ext i j
      simp
    rw [hm, hxe, reindex_exp]
    try rfl
  · rintro ⟨X, hX, hXe⟩
    refine ⟨coords (reindex (eN N) (eN N) (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)), ?_, ?_⟩
    · rw [uToLie_coords]
      exact hX
    · rw [hXe, reindex_exp, skMat_coords]
      rw [Matrix.conjTranspose_reindex, lie_skew X]
      try rfl

lemma volU_pos (N : ℕ) : 0 < volU N := by
  unfold volU
  apply Finset.prod_pos
  intro i _
  positivity

lemma continuous_skMat (N : ℕ) : Continuous (skMat : UCo N → Matrix (Fin N) (Fin N) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [skMat]
  by_cases h1 : a = b
  · simp only [if_pos h1]
    exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst))
  · simp only [if_neg h1]
    by_cases h2 : b < a
    · simp only [dif_pos h2]
      exact (continuous_apply _).comp continuous_snd
    · simp only [dif_neg h2]
      by_cases h3 : a < b
      · simp only [dif_pos h3]
        exact ((continuous_apply _).comp continuous_snd).star.neg
      · simp only [dif_neg h3]
        exact continuous_const

lemma continuous_uToLie (N : ℕ) : Continuous (uToLie (N := N)) := by
  show Continuous fun x : UCo N => (⟨uToLieMat x, uToLieMat_mem x⟩ : Formalism.BasicNotions.lieU N 0)
  exact Continuous.subtype_mk ((continuous_skMat N).matrix_reindex _ _) _

lemma isOpen_ballU (N : ℕ) (r : ℝ) : IsOpen (Formalism.BasicNotions.ballU N 0 r) := by
  have hv : Continuous (fun X : Formalism.BasicNotions.lieU N 0 => (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)) :=
    continuous_subtype_val
  unfold Formalism.BasicNotions.ballU
  exact isOpen_lt (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp ((continuous_apply i).comp hv)).norm) continuous_const

lemma uToLieMat_apply (x : UCo N) (a b : Fin N) : uToLieMat x ((eN N).symm a) ((eN N).symm b) = skMat x a b := by
  simp [uToLieMat]

lemma norm_skMat_lt (x : UCo N) (r : ℝ) (hx : uToLie x ∈ Formalism.BasicNotions.ballU N 0 r) (a b : Fin N) :
    ‖skMat x a b‖ < r := by
  have hx' : ∑ i, ∑ j, ‖uToLieMat x i j‖ < r := hx
  rw [← uToLieMat_apply]
  calc ‖uToLieMat x ((eN N).symm a) ((eN N).symm b)‖
      ≤ ∑ j, ‖uToLieMat x ((eN N).symm a) j‖ :=
        Finset.single_le_sum (f := fun j => ‖uToLieMat x ((eN N).symm a) j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ i, ∑ j, ‖uToLieMat x i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖uToLieMat x i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ _)
    _ < r := hx'

lemma norm_lt_of_mem (x : UCo N) (r : ℝ) (hr : 0 < r) (hx : uToLie x ∈ Formalism.BasicNotions.ballU N 0 r) : ‖x‖ < r := by
  have h1 : ‖x.1‖ < r := by
    refine (pi_norm_lt_iff hr).2 fun a => ?_
    have h5 := norm_skMat_lt x r hx a a
    simpa [skMat] using h5
  have h2 : ‖x.2‖ < r := by
    refine (pi_norm_lt_iff hr).2 ?_
    rintro ⟨⟨a, b⟩, hab⟩
    have h5 := norm_skMat_lt x r hx a b
    simpa [skMat, ne_of_gt hab, hab] using h5
  rw [Prod.norm_def]
  exact max_lt h1 h2

lemma zero_mem_B (r : ℝ) (hr : 0 < r) : (0 : UCo N) ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r := by
  show ∑ i, ∑ j, ‖uToLieMat (0 : UCo N) i j‖ < r
  have h0 : ∀ i j, uToLieMat (0 : UCo N) i j = 0 := by
    intro i j
    simp only [uToLieMat, Matrix.reindex_apply, Matrix.submatrix_apply, skMat]
    split_ifs <;> simp
  simp [h0, hr]

theorem cOmega_pos' (N : ℕ) : 0 < 1 / (2 ^ (N * (N - 1) / 2) * volU N) :=
  div_pos one_pos (mul_pos (by positivity) (volU_pos N))

theorem omegaDensity_main (μ : Measure (Formalism.BasicNotions.UpqT N 0)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    Formalism.BasicNotions.OmegaDensity μ (ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N))) := by
  have hH : (μ.map (iso N)).IsHaarMeasure := (iso N).isHaarMeasure_map μ (continuous_iso N) (continuous_iso_symm N)
  have hP : IsProbabilityMeasure (μ.map (iso N)) :=
    Measure.isProbabilityMeasure_map (continuous_iso N).measurable.aemeasurable
  refine ⟨_, isOmegaLeb_uToLie, ?_⟩
  have hκ : (0 : ℝ) < 2 ^ (N * (N - 1) / 2) := by positivity
  have hV : 0 < volU N := volU_pos N
  have hcpos := cOmega_pos' N
  rw [ENNReal.tendsto_nhds ENNReal.ofReal_ne_top]
  intro ε hε
  obtain ⟨e, he0, he1, he2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have he : 0 < e := ENNReal.ofReal_pos.1 he1
  obtain ⟨δ, hδ, hB⟩ := volU_density (μ.map (iso N)) (e / (1 / (2 ^ (N * (N - 1) / 2) * volU N)))
    (div_pos he hcpos)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hBo : IsOpen (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) := (isOpen_ballU N r).preimage (continuous_uToLie N)
  have hBn : ∀ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, ‖x‖ < δ :=
    fun x hx => (norm_lt_of_mem x r hr.1 hx).trans hr.2
  have hB0 : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ 0 :=
    (hBo.measure_pos volume ⟨0, zero_mem_B r hr.1⟩).ne'
  have hBt : volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => mem_ball_zero_iff.2 (norm_lt_of_mem x r hr.1 hx))
      measure_ball_lt_top)
  have hnum : μ {g | ∃ X ∈ Formalism.BasicNotions.ballU N 0 r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin N ⊕ Fin 0) (Fin N ⊕ Fin 0) ℂ)} =
      μ.map (iso N) {k : UNgrp N | ∃ x ∈ uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r, toM k = NormedSpace.exp (skMat x)} := by
    rw [map_iso_apply, toM_preimage_exp_ball_eq_upqT_exp_ball]
  have hden : (ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) • Measure.map (uToLie (N := N)) volume)
      (Formalism.BasicNotions.ballU N 0 r) = ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) * volume (uToLie ⁻¹' Formalism.BasicNotions.ballU N 0 r) := by
    rw [Measure.smul_apply, Measure.map_apply (continuous_uToLie N).measurable (isOpen_ballU N r).measurableSet,
      smul_eq_mul]
  obtain ⟨hup, hlo⟩ := hB _ hBo.measurableSet hBn
  simp only [Set.mem_Icc]
  rw [hnum, hden]
  have hκ0 : ENNReal.ofReal (2 ^ (N * (N - 1) / 2)) ≠ 0 := (ENNReal.ofReal_pos.2 hκ).ne'
  constructor
  · calc ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) - ε
        ≤ ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) - ENNReal.ofReal e := tsub_le_tsub_left he2.le _
      _ = ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N) - e) := (ENNReal.ofReal_sub _ he.le).symm
      _ ≤ _ := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hκ0 hB0))
          (Or.inl (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt))]
        refine le_trans (le_of_eq ?_) hlo
        rw [← mul_assoc, ← ENNReal.ofReal_mul' hκ.le]
        congr 2
        field_simp
  · calc _ ≤ ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N) + e) := by
          refine ENNReal.div_le_of_le_mul (le_trans hup (le_of_eq ?_))
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
      _ = ENNReal.ofReal (1 / (2 ^ (N * (N - 1) / 2) * volU N)) + ENNReal.ofReal e :=
          ENNReal.ofReal_add hcpos.le he.le
      _ ≤ _ := by gcongr

end PolarCoordinateComparison

end ReciprocityTheory.ChartRestriction.DS
