import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev OmP Mode dM dZ barM sg)
open ReciprocityTheory.ChartRestriction.DS.TRGap (physDet IsPhys)

namespace GlobalTheory.PsCo.PcEF.OmegaDeterminant

variable {n : ℕ}

lemma ev_X_inl (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inl p)) = k p.1 p.2 := by
  simp [ev]

lemma ev_X_inr (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inr p)) = star (k p.1 p.2) := by
  simp [ev]

lemma OmP_apply (ε : Fin n → Bool) (x y : Mode ε) :
    OmP ε x y = (if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inr (y.1.1, x.1.1)) else 0) -
      (if x.1.1 = y.1.1 then MvPolynomial.X (Sum.inr (x.1.2, y.1.2)) else 0) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨j, b⟩, hj, hb⟩ := y
  simp only [OmP, dM, dZ, MvPolynomial.mkDerivation_X, Sum.elim_inr, barM, Matrix.single_apply]
  simp [ite_and, mul_ite, sg]
  simp only at hi ha hj hb
  rcases eq_or_ne a b with rfl | hab <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [apply_ite MvPolynomial.C, mul_ite, ite_mul, Finset.sum_add_distrib, sub_eq_add_neg, *]

lemma ev_OmP (ε : Fin n → Bool) (k : Mat n) (x y : Mode ε) :
    ev k (OmP ε x y) = (if x.1.2 = y.1.2 then star (k y.1.1 x.1.1) else 0) -
      (if x.1.1 = y.1.1 then star (k x.1.2 y.1.2) else 0) := by
  rw [OmP_apply, map_sub, apply_ite (ev k), apply_ite (ev k), ev_X_inr, ev_X_inr, map_zero]

lemma K_block {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {i j : Fin n} (h : ε i ≠ ε j) :
    k i j = 0 := by
  have := congrFun (congrFun hk.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ↓reduceIte, Bool.false_eq_true] at this h
  · exact absurd rfl h
  · linear_combination (1 / 2 : ℂ) * this
  · linear_combination (-1 / 2 : ℂ) * this
  · exact absurd rfl h

lemma K_unit {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (i l : Fin n) :
    ∑ j, k i j * star (k l j) = if i = l then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hk.1) i) l
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this

lemma sum_mode (ε : Fin n → Bool) (f : Fin n × Fin n → ℂ) :
    ∑ y : Mode ε, f y.1 = ∑ j, ∑ b, if ε j = true ∧ ε b = false then f (j, b) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]

lemma entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (x z : Mode ε) :
    ∑ y : Mode ε, (if x.1.2 = y.1.2 then k x.1.1 y.1.1 else 0) *
      ((if y.1.2 = z.1.2 then star (k z.1.1 y.1.1) else 0) -
        (if y.1.1 = z.1.1 then star (k y.1.2 z.1.2) else 0)) =
    (if x = z then 1 else 0) - k x.1.1 z.1.1 * star (k x.1.2 z.1.2) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨l, d⟩, hl, hd⟩ := z
  have hs := sum_mode ε (fun p => (if a = p.2 then k i p.1 else 0) *
      ((if p.2 = d then star (k l p.1) else 0) - (if p.1 = l then star (k p.2 d) else 0)))
  simp only at hs ⊢
  rw [hs]
  have h1 : ∀ j, (∑ b, if ε j = true ∧ ε b = false then (if a = b then k i j else 0) *
      ((if b = d then star (k l j) else 0) - (if j = l then star (k b d) else 0)) else 0) =
      k i j * ((if a = d then star (k l j) else 0) - (if j = l then star (k a d) else 0)) := by
    intro j
    rw [Finset.sum_eq_single a]
    · by_cases hj : ε j = true
      · simp [hj, ha]
      · have : k i j = 0 := K_block hk (by rw [hi]; exact fun h => hj h.symm)
        simp [hj, this]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  by_cases had : a = d
  · subst had
    simp only [if_true, K_unit hk]
    by_cases hil : i = l
    · subst hil; simp
    · simp [hil]
  · simp [had]

def AP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) :=
  fun x y => if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inl (x.1.1, y.1.1)) else 0

end OmegaDeterminant

open OmegaDeterminant in
theorem modeMatrixDet_eq_adjointDet : OmDet := by
  intro n ε
  refine ⟨(AP ε).det, fun k hk => ?_⟩
  let e : Mode ε ≃ {x : Fin n × Fin n // IsPhys ε x} :=
    Equiv.subtypeEquivRight (p := fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false) (fun _ => Iff.rfl)
  have key : (ev k).mapMatrix (AP ε) * (ev k).mapMatrix (OmP ε) =
      (Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
        (if x = y then (1 : ℂ) else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix e e := by
    ext x z
    rw [Matrix.mul_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AP, ev_OmP, Matrix.submatrix_apply, Matrix.of_apply,
      apply_ite (ev k), ev_X_inl, map_zero, e, EmbeddingLike.apply_eq_iff_eq]
    exact entry hk x z
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, key, Matrix.det_submatrix_equiv_self]
  rfl

end GlobalTheory.PsCo.PcEF

end
