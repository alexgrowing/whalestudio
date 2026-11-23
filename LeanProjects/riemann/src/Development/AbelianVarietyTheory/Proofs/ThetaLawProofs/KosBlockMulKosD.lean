import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

def kosBlock {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
    (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R) :
    Matrix (KIx g d N) (KIx g d N) R :=
  Matrix.fromBlocks (Matrix.blockDiagonal' fun I : Finset (Fin g) => C I.card) 0 0 P

section
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

theorem kosBlock_mul (C C' : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P P' : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) * kosBlock C' P' =
      kosBlock (fun j => C j * C' j) (P * P') := by
  simp [kosBlock, Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal'_mul]

theorem kosBlock_one :
    (kosBlock (fun _ => 1) 1 : Matrix (KIx g d N) (KIx g d N) R) = 1 := by
  have : (Matrix.blockDiagonal' fun I : Finset (Fin g) =>
      (1 : Matrix (Fin (N I.card)) (Fin (N I.card)) R)) = 1 := Matrix.blockDiagonal'_one
  rw [kosBlock, this, Matrix.fromBlocks_one]

theorem kosBlock_graded (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (p q : KIx g d N) (h : kdeg p ≠ kdeg q) : kosBlock C P p q = 0 := by
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · have : I ≠ J := by rintro rfl; exact h rfl
    simp [kosBlock, Matrix.blockDiagonal'_apply_ne _ _ _ this]
  · simp [kosBlock]
  · simp [kosBlock]
  · exact absurd rfl h

theorem kosBlock_det (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R) :
    (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).det =
      (∏ j ∈ Finset.range (g + 1), (C j).det ^ g.choose j) * P.det := by
  rw [kosBlock, Matrix.det_fromBlocks_zero₂₁, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']
  congr 1
  rw [← Finset.powerset_univ, Finset.prod_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => (C j).det), Finset.prod_const, Finset.card_powersetCard]
  · simp
  · intro I hI
    rw [(Finset.mem_powersetCard.mp hI).2]

theorem kosBlock_congr (C C' : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R)
    (P P' : Matrix (Fin d) (Fin d) R) (p q : KIx g d N)
    (h1 : ∀ j, kdeg p = j + 1 → C j = C' j) (h2 : kdeg p = 0 → P = P') :
    kosBlock C P p q = kosBlock C' P' p q := by
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · simp only [kosBlock, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal'_apply]
    rw [h1 I.card rfl]
  · simp [kosBlock]
  · simp [kosBlock]
  · rw [h2 rfl]; simp [kosBlock]

theorem kosBlock_det_sub (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (s : ℕ → Prop) [DecidablePred s] :
    ((kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).submatrix
        (fun p : {p // s (kdeg p)} => p.1) (fun p : {p // s (kdeg p)} => p.1)).det =
      (∏ j ∈ Finset.range (g + 1), if s (j + 1) then (C j).det ^ g.choose j else 1) *
        (if s 0 then P.det else 1) := by
  have h := Matrix.twoBlockTriangular_det
    (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => s (kdeg p))
    (fun i hi j hj => kosBlock_graded _ _ _ _ (fun h => hi (h ▸ hj)))
  have e1 : Matrix.toSquareBlockProp
      (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => s (kdeg p)) =
      (kosBlock C P : Matrix (KIx g d N) (KIx g d N) R).submatrix
        (fun p : {p // s (kdeg p)} => p.1) (fun p : {p // s (kdeg p)} => p.1) := by
    ext p q
    exact kosBlock_congr (fun j => if s (j + 1) then C j else 1) C (if s 0 then P else 1) P p.1 q.1
      (fun j hj => if_pos (hj ▸ p.2)) (fun hj => if_pos (hj ▸ p.2))
  have e2 : Matrix.toSquareBlockProp
      (kosBlock (fun j => if s (j + 1) then C j else 1) (if s 0 then P else 1) :
      Matrix (KIx g d N) (KIx g d N) R) (fun p => ¬ s (kdeg p)) = 1 := by
    rw [← Matrix.submatrix_one (fun p : {p : KIx g d N // ¬ s (kdeg p)} => p.1)
      Subtype.val_injective, ← kosBlock_one]
    ext p q
    exact kosBlock_congr (fun j => if s (j + 1) then C j else 1) (fun _ => 1) (if s 0 then P else 1) 1
      p.1 q.1 (fun j hj => if_neg (hj ▸ p.2)) (fun hj => if_neg (hj ▸ p.2))
  rw [e1, e2, Matrix.det_one, mul_one, kosBlock_det] at h
  rw [← h]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · split_ifs <;> simp

theorem kosBlock_mul_inl (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (I : Finset (Fin g)) (a : Fin (N I.card)) (q : KIx g d N) :
    (kosBlock C P * D : Matrix (KIx g d N) (KIx g d N) R) (.inl ⟨I, a⟩) q = ∑ c, C I.card a c * D (.inl ⟨I, c⟩) q := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.sum_eq_single I]
  · simp [kosBlock]
  · intro J _ hJ
    simp [kosBlock, Matrix.blockDiagonal'_apply_ne _ _ _ hJ.symm]
  · simp

theorem kosBlock_mul_inr (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (a : Fin d) (q : KIx g d N) :
    (kosBlock C P * D : Matrix (KIx g d N) (KIx g d N) R) (.inr a) q = ∑ c, P a c * D (.inr c) q := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [kosBlock]

theorem mul_kosBlock_inl (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (I : Finset (Fin g)) (a : Fin (N I.card)) (q : KIx g d N) :
    (D * kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) q (.inl ⟨I, a⟩) = ∑ c, D q (.inl ⟨I, c⟩) * C I.card c a := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sigma, Finset.sum_eq_single I]
  · simp [kosBlock]
  · intro J _ hJ
    simp [kosBlock, Matrix.blockDiagonal'_apply_ne _ _ _ hJ]
  · simp

theorem mul_kosBlock_inr (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (D : Matrix (KIx g d N) (KIx g d N) R) (a : Fin d) (q : KIx g d N) :
    (D * kosBlock C P : Matrix (KIx g d N) (KIx g d N) R) q (.inr a) = ∑ c, D q (.inr c) * P c a := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp [kosBlock]

theorem kosBlock_mul_kosD (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (C : ∀ j, Matrix (Fin (N j)) (Fin (N j)) R) (P : Matrix (Fin d) (Fin d) R)
    (hm : ∀ i j, j < g → C j * m' i j (j + 1) = m i j (j + 1) * C (j + 1))
    (he : P * ev' 0 = ev 0 * C 0) :
    (kosBlock C P * kosD m' ev' : Matrix (KIx g d N) (KIx g d N) R) = kosD m ev * kosBlock C P := by
  have hm' : ∀ i j j', j < g → j' = j + 1 → C j * m' i j j' = m i j j' * C j' := by
    rintro i j _ hj rfl; exact hm i j hj
  ext p q
  rcases p with ⟨I, a⟩ | a <;> rcases q with ⟨J, b⟩ | b
  · rw [kosBlock_mul_inl, mul_kosBlock_inl]
    simp only [kosD, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin (N J.card)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ∉ I ∧ J = insert i I
    · have hc : J.card = I.card + 1 := by rw [h.2, Finset.card_insert_of_notMem h.1]
      have hl : I.card < g := by
        have := Finset.card_le_univ J
        simp only [Fintype.card_fin] at this
        omega
      have := congrFun (congrFun (hm' i _ _ hl hc) a) b
      simp only [Matrix.mul_apply] at this
      simp only [if_pos h, mul_left_comm (C _ _ _), mul_assoc, ← Finset.mul_sum, this]
    · simp only [if_neg h, mul_zero, zero_mul, Finset.sum_const_zero]
  · rw [kosBlock_mul_inl, mul_kosBlock_inr]
    simp [kosD]
  · rw [kosBlock_mul_inr, mul_kosBlock_inl]
    by_cases h : J = ∅
    · subst h
      have he' : P * ev' (∅ : Finset (Fin g)).card =
          ev (∅ : Finset (Fin g)).card * C (∅ : Finset (Fin g)).card := he
      have := congrFun (congrFun he' a) b
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      simp only [kosD, if_true]
      exact this
    · simp [kosD, h]
  · rw [kosBlock_mul_inr, mul_kosBlock_inr]
    simp [kosD]

end

theorem torsSq_kosD_conj : ∀ (R : Type) [CommRing R] (g d : ℕ) (N : ℕ → ℕ) (m m' : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R) (B : ∀ j, (Matrix (Fin (N j)) (Fin (N j)) R)ˣ) (Pm : (Matrix (Fin d) (Fin d) R)ˣ) (t : Rˣ), (∀ i j, j < g → (B j).val * m' i j (j + 1) = m i j (j + 1) * (B (j + 1)).val) → Pm.val * ev' 0 = ev 0 * (B 0).val → IsCx kdeg (kosD m ev) → TorsSq kdeg (kosD m ev) (t : R) → ∃ t' : Rˣ, TorsSq kdeg (kosD m' ev') (t' : R) ∧ t' * (Matrix.GeneralLinearGroup.det Pm) ^ 2 = t * ∏ j ∈ Finset.range (g + 1), (Matrix.GeneralLinearGroup.det (B j)) ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)) := by
  intro R _ g d N m m' ev ev' B Pm t hm he hC hT
  set G : Matrix (KIx g d N) (KIx g d N) R := kosBlock (fun j => (B j).val) Pm.val with hG
  set G' : Matrix (KIx g d N) (KIx g d N) R := kosBlock (fun j => ((B j)⁻¹).val) (Pm⁻¹).val with hG'
  have hGG : G * G' = 1 := by
    rw [hG, hG', kosBlock_mul]; simp only [Units.mul_inv]; exact kosBlock_one
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  have hD : G' * kosD m ev * G = kosD m' ev' := by
    rw [Matrix.mul_assoc, ← kosBlock_mul_kosD m m' ev ev' _ _ hm he, ← Matrix.mul_assoc, hGG',
      Matrix.one_mul]
  obtain ⟨t', h1, h2⟩ := torsSq_conj R _ kdeg (kosD m ev) G G' t (kosBlock_graded _ _) hGG hC hT
  rw [hD] at h1
  rw [hG, kosBlock_det_sub _ _ Even, kosBlock_det_sub _ _ (fun n => ¬ Even n)] at h2
  set u : ℕ → Rˣ := fun j => Matrix.GeneralLinearGroup.det (B j) ^ g.choose j with hu
  set E : Rˣ := ∏ j ∈ Finset.range (g + 1), if Even (j + 1) then u j else 1 with hE
  set O : Rˣ := ∏ j ∈ Finset.range (g + 1), if ¬ Even (j + 1) then u j else 1 with hO
  set p : Rˣ := Matrix.GeneralLinearGroup.det Pm with hp
  have h3 : t' * ((E * p) ^ 2 : Rˣ) = ((t * O ^ 2 : Rˣ) : R) := by
    simp only [Even.zero, if_true, not_true, if_false, mul_one] at h2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, hE, hO, hp, hu, Units.coe_prod,
      apply_ite Units.val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    exact h2
  have h4 : ((t * O ^ 2 * ((E * p) ^ 2)⁻¹ : Rˣ) : R) = t' := by
    rw [Units.val_mul, ← h3, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨t * O ^ 2 * ((E * p) ^ 2)⁻¹, h4 ▸ h1, ?_⟩
  have h5 : ∏ j ∈ Finset.range (g + 1),
      (Matrix.GeneralLinearGroup.det (B j)) ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)) =
      O ^ 2 * (E ^ 2)⁻¹ := by
    rw [hE, hO, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rcases Nat.even_or_odd j with hj | hj
    · have : ¬ Even (j + 1) := by rw [Nat.even_add_one]; simpa using hj
      rw [if_pos this, if_neg this, hj.neg_one_pow, one_pow, inv_one, mul_one, mul_one, hu,
        ← pow_mul, ← zpow_natCast]
      congr 1; push_cast; ring
    · have : Even (j + 1) := hj.add_one
      rw [if_pos this, if_neg (not_not.mpr this), hj.neg_one_pow, one_pow, one_mul, hu,
        ← pow_mul, ← zpow_natCast, ← zpow_neg]
      congr 1; push_cast; ring
  rw [h5, mul_pow, mul_inv, ← mul_assoc, mul_assoc _ (p ^ 2)⁻¹, inv_mul_cancel, mul_one, mul_assoc]

end GlobalTheory.KeyKa
