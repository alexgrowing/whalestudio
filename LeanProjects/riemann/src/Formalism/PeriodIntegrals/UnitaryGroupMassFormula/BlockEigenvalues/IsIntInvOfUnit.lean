import Mathlib
import Formalism.DoubleCosetMeasures.StatementV

noncomputable section

open Matrix

namespace PI.DatumBlockEigen.Unit

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def liftO {m n : Type} (N : Matrix m n F) (h : ∀ i j, N i j ∈ O) : Matrix m n O :=
  Matrix.of fun i j => ⟨N i j, h i j⟩

theorem map_liftO {m n : Type} (N : Matrix m n F) (h : ∀ i j, N i j ∈ O) :
    (liftO O N h).map O.subtype = N := by
  ext i j; rfl

theorem det_liftO {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (h : ∀ i j, N i j ∈ O) : ((liftO O N h).det : F) = N.det := by
  have := RingHom.map_det O.subtype (liftO O N h)
  rw [RingHom.mapMatrix_apply, map_liftO] at this
  exact this

abbrev pI (hϖ : ϖ ∈ O) : Ideal O := Ideal.span {(⟨ϖ, hϖ⟩ : O)}

theorem mem_pI {hϖ : ϖ ∈ O} (x : O) : x ∈ pI O ϖ hϖ ↔ ∃ o ∈ O, (x : F) = ϖ * o := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, c.2, by rw [← hc]; exact mul_comm _ _⟩
  · rintro ⟨o, ho, e⟩
    exact ⟨⟨o, ho⟩, Subtype.ext (by show (o * ϖ : F) = x; rw [e, mul_comm])⟩

variable {O ϖ}

theorem unitO (hϖ : ϖ ∈ O) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) (x : O)
    (hx : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) x)) : (x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (pI O ϖ hϖ)), Ideal.Quotient.eq, mem_pI] at hy
  obtain ⟨c, hc, e⟩ := hy
  have e' : (x : F) * y0 - 1 = ϖ * c := by push_cast at e; exact e
  have hz : ∀ o ∈ O, (x : F) * y0 ≠ ϖ * o := by
    intro o ho h
    apply hL.1
    have h1 : ϖ * (o - c) = 1 := by linear_combination e' - h
    rw [inv_eq_of_mul_eq_one_right h1]
    exact O.sub_mem ho hc
  have hz0 : (x : F) * y0 ≠ 0 := by simpa using hz 0 O.zero_mem
  have hzi : ((x : F) * y0)⁻¹ ∈ O := hL.2 _ (O.mul_mem x.2 y0.2) hz
  have hx0 : (x : F) ≠ 0 := left_ne_zero_of_mul hz0
  have hy0 : (y0 : F) ≠ 0 := right_ne_zero_of_mul hz0
  refine ⟨hx0, ?_⟩
  have : (x : F)⁻¹ = y0 * ((x : F) * y0)⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hy0, mul_one]
  rw [this]
  exact O.mul_mem y0.2 hzi

variable (O) in

theorem isInt_inv {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (hN : ∀ i j, N i j ∈ O) (hdi : N.det⁻¹ ∈ O) : ∀ i j, N⁻¹ i j ∈ O := by
  intro i j
  have hadj : N.adjugate = (liftO O N hN).adjugate.map O.subtype := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, map_liftO]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, smul_eq_mul]
  exact O.mul_mem hdi ((liftO O N hN).adjugate i j).2

theorem isInt_inv_of_unit (hϖ : ϖ ∈ O) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {n : Type} [Fintype n]
    [DecidableEq n] (N : Matrix n n F) (hN : ∀ i j, N i j ∈ O)
    (hu : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) (liftO O N hN).det)) :
    N.det ≠ 0 ∧ ∀ i j, N⁻¹ i j ∈ O := by
  obtain ⟨h0, h1⟩ := unitO hϖ hL _ hu
  rw [det_liftO] at h0 h1
  exact ⟨h0, isInt_inv O N hN h1⟩

variable (O) in

theorem isUnit_det_liftO {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n F)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hAB : A * B = 1) :
    IsUnit (liftO O A hA).det := by
  have e : liftO O A hA * liftO O B hB = 1 := by
    have h : (liftO O A hA * liftO O B hB).map O.subtype = (1 : Matrix n n O).map O.subtype := by
      rw [Matrix.map_mul, map_liftO, map_liftO, hAB]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    exact Matrix.map_injective Subtype.val_injective h
  exact isUnit_iff_exists_inv.mpr ⟨(liftO O B hB).det, by rw [← det_mul, e, det_one]⟩

theorem int_mul {l m n : Type} [Fintype m] {A : Matrix l m F} {B : Matrix m n F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)

theorem II_int {p q : ℕ} (hϖ : ϖ ∈ O) {y : Matrix (Fin p) (Fin q) F}
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) : ∀ i j, y i j ∈ O := fun i j => by
  obtain ⟨o, ho, e⟩ := hy i j
  rw [e]; exact O.mul_mem hϖ ho

theorem II_mul_right {p q r : ℕ} {y : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    {g : Matrix (Fin q) (Fin r) F} (hg : ∀ i j, g i j ∈ O) : y * g ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  choose o ho he using hy
  refine ⟨∑ k, o i k * g k j, O.sum_mem fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  simp only [Matrix.mul_apply, he, Finset.mul_sum, mul_assoc]

theorem II_mul_left {p q r : ℕ} {y : Matrix (Fin q) (Fin r) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    {g : Matrix (Fin p) (Fin q) F} (hg : ∀ i j, g i j ∈ O) : g * y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  choose o ho he using hy
  refine ⟨∑ k, g i k * o k j, O.sum_mem fun k _ => O.mul_mem (hg i k) (ho k j), ?_⟩
  simp only [Matrix.mul_apply, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem II_add {p q : ℕ} {y z : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ)
    (hz : z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) : y + z ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  obtain ⟨o, ho, e⟩ := hy i j
  obtain ⟨o', ho', e'⟩ := hz i j
  exact ⟨o + o', O.add_mem ho ho', by rw [Matrix.add_apply, e, e', mul_add]⟩

theorem II_neg {p q : ℕ} {y : Matrix (Fin p) (Fin q) F} (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) :
    -y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  intro i j
  obtain ⟨o, ho, e⟩ := hy i j
  exact ⟨-o, O.neg_mem ho, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem congOf (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a : ℕ}
    (u : Matrix (Fin a) (Fin a) F) (hu : ∀ i j, u i j ∈ O)
    (h1 : ∀ i j, (ϖ⁻¹ • (u - 1)) i j ∈ O) :
    ∃ U ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a, (U : Matrix (Fin a) (Fin a) F) = u := by
  have hm : (Ideal.Quotient.mk (pI O ϖ hϖ)).mapMatrix (liftO O u hu) = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk (pI O ϖ hϖ)).mapMatrix, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, mem_pI]
    refine ⟨(ϖ⁻¹ • (u - 1)) i j, h1 i j, ?_⟩
    have e1 : (((1 : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 : Matrix (Fin a) (Fin a) F) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [AddSubgroupClass.coe_sub, e1, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hϖ0, one_mul]
    rfl
  have hu1 : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) (liftO O u hu).det) := by
    rw [RingHom.map_det, hm, det_one]; exact isUnit_one
  obtain ⟨hd, hinv⟩ := isInt_inv_of_unit hϖ hL u hu hu1
  exact ⟨Matrix.nonsingInvUnit u (isUnit_iff_ne_zero.mpr hd), ⟨⟨hu, hinv⟩, h1⟩, rfl⟩

theorem shiftJ (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hK : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) (g : J') (y : Matrix (Fin a) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) :
    ∃ U : J', (U : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a ∧
      (((g * U : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) + y := by
  set gi : Matrix (Fin a) (Fin a) F := (((g : GL (Fin a) F)⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
  have hgi : ∀ i j, gi i j ∈ O := (hJ (J'.inv_mem g.2)).1
  have hyI : ∀ i j, (ϖ⁻¹ • y) i j ∈ O := fun i j => by
    obtain ⟨o, ho, e⟩ := hy i j
    rw [Matrix.smul_apply, e, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]; exact ho
  have hu : ∀ i j, (1 + gi * y) i j ∈ O := fun i j => by
    rw [Matrix.add_apply]
    refine O.add_mem ?_ (int_mul hgi (II_int hϖ hy) i j)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, O.one_mem, O.zero_mem]
  have h1 : ∀ i j, (ϖ⁻¹ • ((1 + gi * y) - 1)) i j ∈ O := by
    rw [add_sub_cancel_left, ← Matrix.mul_smul]
    exact int_mul hgi hyI
  obtain ⟨U, hU, hUe⟩ := congOf hϖ hϖ0 hL _ hu h1
  refine ⟨⟨U, hK hU⟩, hU, ?_⟩
  rw [Subgroup.coe_mul, Units.val_mul, hUe, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [show ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * gi = 1 by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.one_mul]

end PI.DatumBlockEigen.Unit
