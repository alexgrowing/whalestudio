import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceMulConjTransposeReal

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge.CdV

variable {n P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

instance borelSpace_lieU (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

section Alg

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)

theorem jpq_eq (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = (Formalism.REAL.Jm ε).submatrix e e := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;>
      simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h, h1, h2, e.injective.eq_iff]
  · simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  · simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  · by_cases h : i = j <;>
      simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h, h1, h2, e.injective.eq_iff]

theorem mem_lieU_iff (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e e ∈ Formalism.BasicNotions.lieU P Q ↔ Formalism.REAL.inG ε X := by
  show (X.submatrix e e)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.submatrix e e = 0 ↔ _
  rw [jpq_eq ε e h1 h2, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inG
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h (e.symm i)) (e.symm j)
    simpa using this
  · intro h
    ext i j
    have := congrFun (congrFun h (e i)) (e j)
    simpa using this

theorem inG_linT (t : EL ε) : Formalism.REAL.inG ε (linT ε t) := by
  rw [linT_apply]
  exact inG_of_gLie ε _

variable (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def phiL : EL ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun t := ⟨(linT ε t).submatrix e e, (mem_lieU_iff ε e h1 h2 _).2 (inG_linT ε t)⟩
  map_add' s t := by
    apply Subtype.ext
    simp [Matrix.submatrix_add]
  map_smul' c t := by
    apply Subtype.ext
    simp [Matrix.submatrix_smul]

theorem phiL_coe (t : EL ε) : ((phiL ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) = (linT ε t).submatrix e e := rfl

include h1 h2 in
theorem inG_back (Y : Formalism.BasicNotions.lieU P Q) :
    Formalism.REAL.inG ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm) := by
  refine (mem_lieU_iff ε e h1 h2 _).1 ?_
  simpa [Matrix.submatrix_submatrix] using Y.2

def phiE : EL ε ≃ₗ[ℝ] Formalism.BasicNotions.lieU P Q :=
  { phiL ε e h1 h2 with
    invFun := fun Y => cM ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm)
    left_inv := fun t => by
      show cM ε (((linT ε t).submatrix e e).submatrix e.symm e.symm) = t
      simpa [Matrix.submatrix_submatrix] using cM_linT ε t
    right_inv := fun Y => by
      apply Subtype.ext
      show (linT ε (cM ε ((Y : Matrix ι ι ℂ).submatrix e.symm e.symm))).submatrix e e = Y
      rw [linT_cM (inG_back ε e h1 h2 Y)]
      simp [Matrix.submatrix_submatrix] }

def phiC : EL ε ≃L[ℝ] Formalism.BasicNotions.lieU P Q := (phiE ε e h1 h2).toContinuousLinearEquiv

theorem phiC_coe (t : EL ε) : ((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) = (linT ε t).submatrix e e := rfl

theorem l1_entries_coordinate_chart (t : EL ε) :
    ∑ i, ∑ j, ‖((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) i j‖ = ∑ a, ∑ b, ‖linT ε t a b‖ := by
  rw [phiC_coe]
  exact Fintype.sum_equiv e _ _ (fun i => Fintype.sum_equiv e _ _ (fun j => rfl))

theorem preimage_ballU (r : ℝ) : (phiC ε e h1 h2) ⁻¹' Formalism.BasicNotions.ballU P Q r = l1B ε r := by
  ext t
  show (∑ i, ∑ j, ‖((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) i j‖ < r) ↔ _
  rw [l1_entries_coordinate_chart]
  rfl

theorem hilbert_schmidt_coordinate_chart (t : EL ε) :
    Cd.hs2 ((phiC ε e h1 h2 t : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) = ‖t‖ ^ 2 := by
  unfold Cd.hs2
  rw [phiC_coe]
  have e1 : ∑ i, ∑ j, Complex.normSq ((linT ε t).submatrix e e i j) = ∑ a, ∑ b, Complex.normSq (linT ε t a b) :=
    Fintype.sum_equiv e _ _ (fun i => Fintype.sum_equiv e _ _ (fun j => rfl))
  rw [e1, linT_apply]
  have hnorm : ‖t‖ = ‖(((obG ε).repr.symm t : gLie ε) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := by
    rw [← LinearIsometryEquiv.norm_map (obG ε).repr.symm t]
    rfl
  rw [hnorm, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Real.norm_eq_abs, sq_abs, Formalism.MainNotions.S.unrealify, Complex.normSq_mk]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg

section Iso

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def mL : EL ε × EL ε →ₗ[ℝ] Matrix ι ι ℂ where
  toFun p := ((phiC ε e h1 h2 p.1 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) +
    Complex.I • ((phiC ε e h1 h2 p.2 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, smul_add]; abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]

theorem mL_apply (p : EL ε × EL ε) : mL ε e h1 h2 p = ((phiC ε e h1 h2 p.1 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) +
    Complex.I • ((phiC ε e h1 h2 p.2 : Formalism.BasicNotions.lieU P Q) : Matrix ι ι ℂ) := rfl

end Iso

def rL : Matrix ι ι ℂ →ₗ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) where
  toFun Z := WithLp.toLp 2 (fun p => if p.2 = 0 then (Z p.1.1 p.1.2).re else (Z p.1.1 p.1.2).im)
  map_add' Z W := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c Z := by
    ext p
    by_cases h : p.2 = 0 <;> simp [h]

theorem rL_apply (Z : Matrix ι ι ℂ) (p : (ι × ι) × Fin 2) :
    rL Z p = if p.2 = 0 then (Z p.1.1 p.1.2).re else (Z p.1.1 p.1.2).im := rfl

theorem norm_rL_sq (Z : Matrix ι ι ℂ) : ‖rL Z‖ ^ 2 = Cd.hs2 Z := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [rL_apply, Real.norm_eq_abs, sq_abs]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold Cd.hs2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Fin.sum_univ_two, Complex.normSq_apply, sq]

section Iso2

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def gL : WithLp 2 (EL ε × EL ε) →ₗ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) :=
  rL.comp ((mL ε e h1 h2).comp (WithLp.linearEquiv 2 ℝ (EL ε × EL ε)).toLinearMap)

theorem gL_apply (w : WithLp 2 (EL ε × EL ε)) : gL ε e h1 h2 w = rL (mL ε e h1 h2 (WithLp.ofLp w)) := rfl

private theorem cross_lemma {A B : Matrix ι ι ℂ} (hA : A ∈ Formalism.BasicNotions.lieU P Q) (hB : B ∈ Formalism.BasicNotions.lieU P Q) :
    Cd.hs2 (A + Complex.I • B) = Cd.hs2 A + Cd.hs2 B := by
  let s : ι → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hJ : Formalism.UG.Jpq P Q = Matrix.diagonal s := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h, s]
    · simp [Formalism.UG.Jpq, Matrix.diagonal_apply, s]
    · simp [Formalism.UG.Jpq, Matrix.diagonal_apply, s]
    · by_cases h : i = j <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h, s]
  have hss : ∀ j, s j * s j = 1 := by
    intro j
    rcases j with j | j <;> simp [s]
  have key : ∀ {M : Matrix ι ι ℂ}, M ∈ Formalism.BasicNotions.lieU P Q → ∀ j k, star (M j k) = -(s k * s j * M k j) := by
    intro M hM j k
    have h := congrFun (congrFun (show Mᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * M = 0 from hM) k) j
    rw [hJ] at h
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at h
    linear_combination (s j) * h - star (M j k) * hss j
  have hT : (∑ j, ∑ k, A j k * star (B j k)).im = 0 := by
    have h1 : star (∑ j, ∑ k, A j k * star (B j k)) = ∑ j, ∑ k, A j k * star (B j k) := by
      simp only [star_sum, star_mul', star_star]
      simp only [key hA, key hB]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    exact Complex.conj_eq_iff_im.1 h1
  have hpt : ∀ j k, Complex.normSq ((A + Complex.I • B) j k) =
      Complex.normSq (A j k) + Complex.normSq (B j k) + 2 * (A j k * star (B j k)).im := by
    intro j k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ∑ j, ∑ k, (A j k * star (B j k)).im = 0 := by
    rw [← hT, Complex.im_sum]
    simp only [Complex.im_sum]
  unfold Cd.hs2
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]

theorem norm_gL (w : WithLp 2 (EL ε × EL ε)) : ‖gL ε e h1 h2 w‖ = ‖w‖ := by
  have hsq : ‖gL ε e h1 h2 w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [gL_apply, norm_rL_sq, mL_apply, cross_lemma (phiC ε e h1 h2 _).2 (phiC ε e h1 h2 _).2, hilbert_schmidt_coordinate_chart, hilbert_schmidt_coordinate_chart,
      WithLp.prod_norm_sq_eq_of_L2]
    rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

private theorem jpq_sq_lemma : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private theorem jpq_herm_lemma_2 : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem a_mem (Z : Matrix ι ι ℂ) :
    ((1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) ∈ Formalism.BasicNotions.lieU P Q := by
  have jj' : ∀ X : Matrix ι ι ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, jpq_sq_lemma, Matrix.one_mul]
  show _ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * _ = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, jpq_herm_lemma_2,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, jj', jpq_sq_lemma, Matrix.mul_one]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, ← smul_add]
  have : Zᴴ * Formalism.UG.Jpq P Q - Formalism.UG.Jpq P Q * Z + (Formalism.UG.Jpq P Q * Z - Zᴴ * Formalism.UG.Jpq P Q) = 0 := by abel
  rw [this, smul_zero]

theorem b_mem (Z : Matrix ι ι ℂ) :
    ((-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) ∈ Formalism.BasicNotions.lieU P Q := by
  have jj' : ∀ X : Matrix ι ι ℂ, Formalism.UG.Jpq P Q * (Formalism.UG.Jpq P Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, jpq_sq_lemma, Matrix.one_mul]
  show _ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * _ = 0
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, jpq_herm_lemma_2,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, jj', jpq_sq_lemma, Matrix.mul_one]
  have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by
    first | (simp [Complex.conj_I]; done) | (simp [Complex.conj_I]; ring)
  rw [hs, neg_smul, add_comm (Formalism.UG.Jpq P Q * Z) (Zᴴ * Formalism.UG.Jpq P Q), add_neg_cancel]

theorem ab_sum (Z : Matrix ι ι ℂ) :
    (1 / 2 : ℂ) • (Z - Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) +
      Complex.I • ((-(Complex.I / 2)) • (Z + Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q)) = Z := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (-(Z i j + (Formalism.UG.Jpq P Q * Zᴴ * Formalism.UG.Jpq P Q) i j) / 2) * Complex.I_sq

theorem gL_surj : Function.Surjective (gL ε e h1 h2) := by
  intro y
  let Z : Matrix ι ι ℂ := fun i j => (y ((i, j), 0) : ℂ) + (y ((i, j), 1) : ℂ) * Complex.I
  let A : Formalism.BasicNotions.lieU P Q := ⟨_, a_mem Z⟩
  let B : Formalism.BasicNotions.lieU P Q := ⟨_, b_mem Z⟩
  refine ⟨WithLp.toLp 2 ((phiC ε e h1 h2).symm A, (phiC ε e h1 h2).symm B), ?_⟩
  rw [gL_apply, WithLp.ofLp_toLp, mL_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [show ((A : Matrix ι ι ℂ) + Complex.I • (B : Matrix ι ι ℂ)) = Z from ab_sum Z]
  ext p
  rw [rL_apply]
  rcases p with ⟨⟨i, j⟩, k⟩
  fin_cases k <;> simp [Z]

def gI : WithLp 2 (EL ε × EL ε) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((ι × ι) × Fin 2) :=
  LinearIsometryEquiv.ofSurjective { toLinearMap := gL ε e h1 h2, norm_map' := norm_gL ε e h1 h2 } (gL_surj ε e h1 h2)

theorem gI_apply (w : WithLp 2 (EL ε × EL ε)) : gI ε e h1 h2 w = gL ε e h1 h2 w := rfl

end Iso2

section Meas

def MpCF (κ : Type) [Fintype κ] : Prop :=
  MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
    volume volume

variable (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)

def aF (p : EL ε × EL ε) : (ι × ι) → ℂ := Formalism.BasicNotions.entries (mL ε e h1 h2 p)

private theorem mpT_lemma (m : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod volume) volume := by
  have hA := (PiLp.volume_preserving_ofLp (Fin m)).prod (PiLp.volume_preserving_ofLp (Fin m))
  have hB := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin m => (volume : Measure ℝ))
  have hC := PiLp.volume_preserving_toLp (Fin m ⊕ Fin m)
  have hJ := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin m ⊕ Fin m => ℝ)).measurePreserving
  have := hJ.comp (hC.comp (hB.comp hA))
  convert this using 1
  all_goals first | rfl | (funext p; rfl)

theorem mp_aF (hC : MpCF (ι × ι)) :
    MeasurePreserving (aF ε e h1 h2) ((volume : Measure (EL ε)).prod volume) volume := by
  have hT := mpT_lemma (dimL ε)
  have hG := (gI ε e h1 h2).measurePreserving
  have := MeasurePreserving.comp hC (hG.comp hT)
  convert this using 1
  funext p
  funext k
  simp only [Function.comp_apply, gI_apply, gL_apply, WithLp.ofLp_toLp, aF, Formalism.BasicNotions.entries, rL_apply]
  simp [Complex.re_add_im]

theorem lamVol_of (hC : MpCF (ι × ι)) : LamVol ε e := by
  intro h1 h2 lam hlam r
  have hcl : IsClosed ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ)) := by
    have : ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ)) =
        {X | Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0} := rfl
    rw [this]
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)) continuous_const
  haveI : LocallyCompactSpace (Matrix ι ι ℂ) := inferInstanceAs (LocallyCompactSpace (ι → ι → ℂ))
  haveI : SecondCountableTopology (Matrix ι ι ℂ) := inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))
  haveI : SecondCountableTopology (Formalism.BasicNotions.lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology ((Formalism.BasicNotions.lieU P Q : Submodule ℝ (Matrix ι ι ℂ)) : Set (Matrix ι ι ℂ))
  haveI : LocallyCompactSpace (Formalism.BasicNotions.lieU P Q) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := hlam.1
  have hφm : Measurable (phiC ε e h1 h2) := (phiC ε e h1 h2).continuous.measurable
  haveI hH : ((volume : Measure (EL ε)).map (phiC ε e h1 h2)).IsAddHaarMeasure := by
    first
    | infer_instance
    | exact (phiC ε e h1 h2).isAddHaarMeasure_map volume
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, lam = c • (volume : Measure (EL ε)).map (phiC ε e h1 h2) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul lam _⟩
  have hνν : ((volume : Measure (EL ε)).map (phiC ε e h1 h2)).prod ((volume : Measure (EL ε)).map (phiC ε e h1 h2)) =
      ((volume : Measure (EL ε)).prod volume).map (Prod.map (phiC ε e h1 h2) (phiC ε e h1 h2)) :=
    Measure.map_prod_map _ _ hφm hφm
  have hA : Continuous fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q => (ab.1 : Matrix ι ι ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hB : Continuous fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q => (ab.2 : Matrix ι ι ℂ) :=
    continuous_subtype_val.comp continuous_snd
  have hF' : Continuous (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
      (ab.1 : Matrix ι ι ℂ) + Complex.I • (ab.2 : Matrix ι ι ℂ)) := hA.add (hB.const_smul Complex.I)
  have hF : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix ι ι ℂ) + Complex.I • (ab.2 : Matrix ι ι ℂ))) :=
    (continuous_pi fun k : ι × ι => hF'.matrix_elem k.1 k.2).measurable
  have h := hlam.2
  rw [hc, Measure.prod_smul_left, Measure.prod_smul_right, hνν, Measure.map_smul, Measure.map_smul,
    Measure.map_map hF (hφm.prodMap hφm)] at h
  change c • c • Measure.map (aF ε e h1 h2) ((volume : Measure (EL ε)).prod volume) = volume at h
  rw [(mp_aF ε e h1 h2 hC).map_eq] at h
  have hK : 0 < volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1) := Metric.measure_closedBall_pos _ _ one_pos
  have hK' : volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  have hx : 0 < (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal := ENNReal.toReal_pos hK.ne' hK'
  have hv := congrArg (fun μ : Measure ((ι × ι) → ℂ) => (μ (Metric.closedBall 0 1)).toReal) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at hv
  have hcc : ((c : ℝ) * c) = 1 := by
    have h3 : ((c : ℝ) * c) * (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal =
        1 * (volume (Metric.closedBall (0 : (ι × ι) → ℂ) 1)).toReal := by
      rw [one_mul]
      linear_combination hv
    exact mul_right_cancel₀ hx.ne' h3
  have hc1 : c = 1 := by
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have hballm : MeasurableSet (Formalism.BasicNotions.ballU P Q r) := by
    apply IsOpen.measurableSet
    apply isOpen_lt _ continuous_const
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_subtype_val.matrix_elem i j).norm
  rw [hc, hc1, one_smul, Measure.map_apply hφm hballm, preimage_ballU]

end Meas

end Formalism.MainNotions.S.Gauge.CdV
