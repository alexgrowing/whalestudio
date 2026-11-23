import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensStepOf

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

section cx

variable {n : ℕ}

def cay {R : Type*} [CommRing R] (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := (1 - X) * (1 + X)⁻¹

theorem det_one_add_ne_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : (1 + X).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hXv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : X *ᵥ v = -v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hXv
    exact (neg_eq_of_add_eq_zero_right hXv).symm
  have h2 : Xᴴ *ᵥ v = v := by rw [hX, Matrix.neg_mulVec, h1, neg_neg]
  have h3 : star v ᵥ* X = star v := by
    have := Matrix.star_mulVec Xᴴ v
    rw [Matrix.conjTranspose_conjTranspose, h2] at this
    exact this.symm
  have h4 : star v ⬝ᵥ v = -(star v ⬝ᵥ v) := by
    calc star v ⬝ᵥ v = (star v ᵥ* X) ⬝ᵥ v := by rw [h3]
      _ = star v ⬝ᵥ (X *ᵥ v) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = -(star v ⬝ᵥ v) := by rw [h1, dotProduct_neg]
  have h5 : star v ⬝ᵥ v = 0 := by linear_combination h4 / 2
  exact hv (dotProduct_star_self_eq_zero.1 h5)

theorem isUnit_det_one_add {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr (det_one_add_ne_zero hX)

theorem isUnit_det_one_sub {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : IsUnit (1 - X).det := by
  have h : (-X)ᴴ = -(-X) := by rw [Matrix.conjTranspose_neg, hX]
  rw [sub_eq_add_neg]
  exact isUnit_det_one_add h

theorem cay_mul_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : cay X * (cay X)ᴴ = 1 := by
  have h1 : (1 + X)ᴴ = 1 - X := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX, sub_eq_add_neg]
  have h2 : (1 - X)ᴴ = 1 + X := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX, sub_neg_eq_add]
  have hu1 := isUnit_det_one_add hX
  have hu2 := isUnit_det_one_sub hX
  have hc : Commute (1 - X) (1 + X) :=
    (Commute.one_right (1 - X)).add_right ((Commute.one_left X).sub_left (Commute.refl X))
  have e : (1 + X)⁻¹ * (1 - X)⁻¹ = (1 - X)⁻¹ * (1 + X)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hc.eq, Matrix.mul_inv_rev]
  unfold cay
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, h1, h2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + X)⁻¹ (1 - X)⁻¹, e, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1,
    Matrix.mul_one, Matrix.mul_nonsing_inv _ hu2]

theorem cay_eq (X : Matrix (Fin n) (Fin n) ℂ) :
    cay X = ((1 + X).det)⁻¹ • ((1 - X) * (1 + X).adjugate) := by
  unfold cay
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]

theorem exists_cay {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ * Y = 1) (h1 : (1 + Y).det ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X ∧ cay X = Y := by
  have hA : IsUnit (1 + Y).det := isUnit_iff_ne_zero.mpr h1
  have hYY : Y * Yᴴ = 1 := by
    first
      | exact mul_eq_one_comm.1 hY
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hY
  have hc : Commute (1 + Y) (Y - 1) :=
    ((Commute.one_left Y).add_left (Commute.refl Y)).sub_right (Commute.one_right _)
  have hcinv : (1 + Y)⁻¹ * (Y - 1) = (Y - 1) * (1 + Y)⁻¹ := by
    calc (1 + Y)⁻¹ * (Y - 1) = (1 + Y)⁻¹ * (Y - 1) * ((1 + Y) * (1 + Y)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      _ = (1 + Y)⁻¹ * ((1 + Y) * (Y - 1)) * (1 + Y)⁻¹ := by
          rw [hc.eq]
          simp only [Matrix.mul_assoc]
      _ = (Y - 1) * (1 + Y)⁻¹ := by
          rw [← Matrix.mul_assoc (1 + Y)⁻¹, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  refine ⟨(1 - Y) * (1 + Y)⁻¹, ?_, ?_⟩
  · have hinv : ((1 + Y)ᴴ)⁻¹ = (1 + Y)⁻¹ * Y := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, ← Matrix.mul_assoc]
      have e : 1 + Yᴴ = Yᴴ * (1 + Y) := by
        rw [Matrix.mul_add, Matrix.mul_one, hY, add_comm]
      rw [e, Matrix.mul_assoc Yᴴ, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one, hY]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hinv, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hYY, hcinv,
      ← neg_mul, neg_sub]
  · have hsum : 1 + (1 - Y) * (1 + Y)⁻¹ = (2 : ℂ) • (1 + Y)⁻¹ := by
      calc 1 + (1 - Y) * (1 + Y)⁻¹ = (1 + Y) * (1 + Y)⁻¹ + (1 - Y) * (1 + Y)⁻¹ := by
            rw [Matrix.mul_nonsing_inv _ hA]
        _ = ((1 + Y) + (1 - Y)) * (1 + Y)⁻¹ := (Matrix.add_mul _ _ _).symm
        _ = (2 : ℂ) • (1 + Y)⁻¹ := by
            rw [show (1 + Y) + (1 - Y) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) by
              rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
    have hdiff : 1 - (1 - Y) * (1 + Y)⁻¹ = (2 : ℂ) • (Y * (1 + Y)⁻¹) := by
      calc 1 - (1 - Y) * (1 + Y)⁻¹ = (1 + Y) * (1 + Y)⁻¹ - (1 - Y) * (1 + Y)⁻¹ := by
            rw [Matrix.mul_nonsing_inv _ hA]
        _ = ((1 + Y) - (1 - Y)) * (1 + Y)⁻¹ := (Matrix.sub_mul _ _ _).symm
        _ = (2 : ℂ) • (Y * (1 + Y)⁻¹) := by
            rw [show (1 + Y) - (1 - Y) = (2 : ℂ) • Y by rw [two_smul]; abel, Matrix.smul_mul]
    have hinv2 : ((2 : ℂ) • (1 + Y)⁻¹)⁻¹ = (2 : ℂ)⁻¹ • (1 + Y) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hA,
        mul_inv_cancel₀ two_ne_zero, one_smul]
    unfold cay
    rw [hsum, hdiff, hinv2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ two_ne_zero,
      one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

end cx

section pts

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

def cpt (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else star (Y (InfinitePlace.mk p.1) p.2.1 p.2.2)

theorem repPt_eq_cpt (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (hY : ∀ w, (Y w)ᴴ * Y w = 1) :
    repPt Y = cpt Y := by
  unfold repPt
  funext p
  simp only [cpt]
  split_ifs
  · rfl
  · rw [Matrix.inv_eq_left_inv (hY _), Matrix.conjTranspose_apply]

theorem denseRange_emb [IsCMField L] :
    DenseRange (fun x : L => fun w : InfinitePlace L => w.embedding x) := by
  have hcx : ∀ w : InfinitePlace L, w.IsComplex := fun w => by
    first
    | exact NumberField.IsTotallyComplex.isComplex w
    | exact IsTotallyComplex.isComplex w
  have hd : DenseRange (algebraMap L (InfiniteAdeleRing L)) :=
    InfiniteAdeleRing.denseRange_algebraMap L
  let g : InfiniteAdeleRing L → (InfinitePlace L → ℂ) := fun a w =>
    InfinitePlace.Completion.extensionEmbedding w (a w)
  have hg : Continuous g :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w)
  have hs : Function.Surjective g := by
    intro y
    have h : ∀ w, ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = y w := fun w =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (hcx w) (y w)
    choose a ha using h
    exact ⟨a, funext ha⟩
  have h := hs.denseRange.comp hd hg
  convert h using 1
  funext x
  funext w
  simp only [Function.comp_apply, g]
  first
  | exact (InfinitePlace.Completion.extensionEmbedding_coe w _).symm
  | exact (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.equiv w |>.symm x)).symm
  | simp [InfinitePlace.Completion.extensionEmbedding_coe]
  | rfl

theorem denseRange_matEmb [IsCMField L] :
    DenseRange (fun b : Matrix (Fin n) (Fin n) L => fun (i j : Fin n) (w : InfinitePlace L) => w.embedding (b i j)) := by
  exact DenseRange.piMap fun _ => DenseRange.piMap fun _ => denseRange_emb

def skewOf (z : Fin n → Fin n → InfinitePlace L → ℂ) (w : InfinitePlace L) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => z i j w) - (Matrix.of (fun i j => z i j w))ᴴ

theorem skewOf_skew (z : Fin n → Fin n → InfinitePlace L → ℂ) (w : InfinitePlace L) :
    (skewOf z w)ᴴ = -(skewOf z w) := by
  unfold skewOf
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem continuous_cpt_cay :
    Continuous (fun z : Fin n → Fin n → InfinitePlace L → ℂ => cpt (fun w => cay (skewOf z w))) := by
  have hs : ∀ w : InfinitePlace L,
      Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => skewOf z w := by
    intro w
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [skewOf, Matrix.sub_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
    have hc : ∀ a b : Fin n, Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => z a b w :=
      fun a b => (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
    first
      | exact (hc i j).sub (hc j i).star
      | fun_prop
  have hA : ∀ (w : InfinitePlace L) (i j : Fin n),
      Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => cay (skewOf z w) i j := by
    intro w i j
    have e : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => cay (skewOf z w) i j) = fun z =>
        ((1 + skewOf z w).det)⁻¹ * ((1 - skewOf z w) * (1 + skewOf z w).adjugate) i j := by
      funext z
      rw [cay_eq, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    have hd : Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => (1 + skewOf z w).det :=
      (continuous_const.add (hs w)).matrix_det
    refine (hd.inv₀ fun z => det_one_add_ne_zero (skewOf_skew z w)).mul ?_
    exact (((continuous_const.sub (hs w)).matrix_mul
      (continuous_const.add (hs w)).matrix_adjugate)).matrix_elem i j
  refine continuous_pi fun p => ?_
  simp only [cpt]
  split_ifs
  · exact hA _ _ _
  · exact (hA _ _ _).star

end pts

end PI.UnitaryGroupMassFormula.HwConjInf
