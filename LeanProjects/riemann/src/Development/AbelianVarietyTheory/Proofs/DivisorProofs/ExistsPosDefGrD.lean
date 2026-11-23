import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.SchurRow

theorem schur {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (M : Matrix (A ⊕ B) (A ⊕ B) ℂ)
    (hM : M.PosDef) : ∃ Q : Matrix B B ℂ, Q.PosDef ∧ Q.det * M.toBlocks₁₁.det = M.det ∧ ∀ w : B → ℂ,
      (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b) * M *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b))ᴴ).det =
        M.toBlocks₁₁.det * ∑ a, ∑ b, w a * Q a b * star (w b) := by
  have h11 : M.toBlocks₁₁.PosDef := hM.submatrix Sum.inl_injective
  have e : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    ext (a | a) (b | b) <;> try rfl
    exact (hM.isHermitian.apply _ _).symm
  generalize M.toBlocks₁₁ = P at h11 e
  generalize M.toBlocks₁₂ = R at e
  generalize M.toBlocks₂₂ = S at e
  subst e
  have := h11.isUnit.invertible
  have hd := Matrix.det_fromBlocks₁₁ P R Rᴴ S
  rw [Matrix.invOf_eq_nonsing_inv] at hd
  refine ⟨S - Rᴴ * P⁻¹ * R, ?_, by rw [hd, mul_comm], fun w => ?_⟩
  · refine ((h11.fromBlocks₁₁ R S).1 hM.posSemidef).posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := hM.det_pos.ne'
    rw [hd] at this
    exact (right_ne_zero_of_mul this).isUnit
  · generalize hW : (Matrix.of fun (_ : Unit) b => w b) = W
    have : Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W * Matrix.fromBlocks P R Rᴴ S *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W)ᴴ = Matrix.fromBlocks P (R * Wᴴ) (W * Rᴴ) (W * S * Wᴴ) := by
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    rw [this, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have e2 : W * S * Wᴴ - W * Rᴴ * P⁻¹ * (R * Wᴴ) = W * (S - Rᴴ * P⁻¹ * R) * Wᴴ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [e2]
    congr 1
    rw [Matrix.det_unique, Finset.sum_comm]
    subst hW
    generalize S - Rᴴ * P⁻¹ * R = Q
    simp [Matrix.mul_apply, Finset.sum_mul]

noncomputable def ixA {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Option {j : Low s // j.1.2 = i} ≃ Fin s :=
  Equiv.ofBijective (Sum.elim Subtype.val fun b => Option.elim b i fun j => j.1.1.1) (by
    constructor
    · rintro (⟨a, ha⟩ | _ | ⟨⟨⟨a, a'⟩, ha⟩, h'⟩) (⟨b, hb⟩ | _ | ⟨⟨⟨b, b'⟩, hb⟩, h⟩) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Option.elim] at e <;> (try dsimp only at h) <;>
        (try dsimp only at h') <;> (try dsimp only at ha) <;> (try dsimp only at hb) <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · intro c
      rcases lt_trichotomy c i with h | h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr none, h.symm⟩, ⟨.inr (some ⟨⟨(c, i), h⟩, rfl⟩), rfl⟩])

noncomputable def ixB {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Unit ≃ {a : Fin s // (a : ℕ) < i + 1} :=
  Equiv.ofBijective (Sum.elim (fun a => ⟨a.1, a.2.trans (Nat.lt_succ_self _)⟩) fun _ => ⟨i, Nat.lt_succ_self _⟩) (by
    constructor
    · rintro (⟨a, ha⟩ | _) (⟨b, hb⟩ | _) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at e <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · rintro ⟨c, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr (), Subtype.ext (Fin.ext h.symm)⟩])

theorem det_upU {s : ℕ} (y : Low s → ℂ) : (upU y).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upU]
  · intro a b h
    have h : b < a := h
    simp [upU, h.not_gt, h.ne']

theorem row_lt {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) {a : Fin s}
    (ha : a < i) : upU y' a = upU (fun j => if j.1.2 < i then y j else 0) a := by
  funext c
  simp only [upU, Matrix.of_apply]
  split_ifs with h1
  · exact h _ ha
  all_goals rfl

theorem row_ge {s : ℕ} {i : Fin s} (y : Low s → ℂ) {a : Fin s} (ha : i ≤ a) (c : Fin s) :
    upU (fun j => if j.1.2 < i then y j else 0) a c = if a = c then 1 else 0 := by
  simp only [upU, Matrix.of_apply, ha.not_gt, if_false]
  split_ifs with h1 h2
  · exact absurd h2 h1.ne
  all_goals rfl

theorem rows_eq {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) :
    (upU y').submatrix (fun a => (ixB i a).1) id =
      Matrix.fromBlocks 1 0 0 (Matrix.of fun (_ : Unit) (b : Option {j : Low s // j.1.2 = i}) =>
        (Option.elim b 1 (fun b => y' b.1) : ℂ)) *
        (upU (fun j => if j.1.2 < i then y j else 0)).submatrix (ixA i) id := by
  refine Matrix.ext ?_
  rintro (a | a) c <;> refine Eq.trans ?_ Matrix.mul_apply.symm
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.submatrix_apply, id]
    exact congrFun (row_lt h a.2) c
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.submatrix_apply, id, Matrix.of_apply]
    have hr : ∀ b, upU (fun j => if j.1.2 < i then y j else 0) (ixA i (.inr b)) c =
        if ixA i (.inr b) = c then 1 else 0 := by
      rintro (_ | ⟨j, rfl⟩)
      exacts [row_ge y le_rfl c, row_ge y (le_of_lt j.2) c]
    simp only [hr]
    change upU y' i c = _
    obtain ⟨c | c, rfl⟩ := (ixA i).surjective c
    · have h1 : ixA i (.inl c) < i := c.2
      simp [upU, h1.not_gt, h1.ne']
    · simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      obtain _ | ⟨⟨⟨b, a⟩, hab⟩, rfl⟩ := c
      · change upU y' i i = 1
        simp [upU]
      · exact dif_pos hab

theorem conj_mul {A B C : Type} [Fintype B] [Fintype C] (W : Matrix A B ℂ) (R : Matrix B C ℂ) (G : Matrix C C ℂ) :
    W * R * G * (W * R)ᴴ = W * (R * G * Rᴴ) * Wᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.FlagCell2.SchurRow

open GlobalTheory.FlagCell2.SchurRow in

theorem GlobalTheory.FlagCell2.exists_posDef_grD : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re := by
  intro s G hG y i
  set U := upU (fun j : Low s => if j.1.2 < i then y j else 0) with hU
  have hdU : U.det = 1 := det_upU _
  have hM0 : (U * G * Uᴴ).PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by simp [hdU])))
  have hM : ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).PosDef := hM0.submatrix (ixA i).injective
  obtain ⟨Q, hQ, hdet, hw⟩ := schur _ hM
  have hpos : 0 < ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := (hM.submatrix Sum.inl_injective).det_pos
  have h11 : ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → leadMinor (upU y' * G * (upU y')ᴴ) i =
      ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := fun y' h => by
    unfold leadMinor
    congr 1
    ext a b
    change (upU y' * G * (upU y')ᴴ) a b = (U * G * Uᴴ) a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, row_lt h a.2, row_lt h b.2, hU]
  refine ⟨Q, hQ, ?_, fun y' h => ?_⟩
  · rw [h11 y fun _ _ => rfl, hdet, Matrix.det_submatrix_equiv_self]
    simp [hdU]
  · have e := hw fun b => Option.elim b 1 (fun b => y' b.1)
    replace e : leadMinor (upU y' * G * (upU y')ᴴ) (i + 1) = _ := Eq.trans (by
      unfold leadMinor
      rw [← Matrix.det_submatrix_equiv_self (ixB i)]
      congr 1
      have e1 : (U * G * Uᴴ).submatrix (ixA i) (ixA i) = U.submatrix (ixA i) id * G * (U.submatrix (ixA i) id)ᴴ := rfl
      have e2 : ((upU y' * G * (upU y')ᴴ).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i + 1} → Fin s)
          Subtype.val).submatrix (ixB i) (ixB i) =
          (upU y').submatrix (fun a => (ixB i a).1) id * G * ((upU y').submatrix (fun a => (ixB i a).1) id)ᴴ := rfl
      rw [e1, e2, rows_eq h]
      exact conj_mul _ _ _) e
    rw [grD, e, h11 y' h]
    generalize ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det = d at hpos
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hpos
    rw [Complex.mul_re, ← h2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h1.ne']
