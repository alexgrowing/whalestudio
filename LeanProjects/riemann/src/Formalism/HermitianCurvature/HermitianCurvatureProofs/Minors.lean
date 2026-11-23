import Formalism.HermitianCurvature.Statement

namespace Formalism.FourierDecayAlt.P.Minors

open Matrix

variable {K : Type} [Field K]

def Lead (r : ℕ) (C : Matrix (Fin r) (Fin r) K) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ r), (C.submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0

def border {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) d u j)
      (fun i' => Fin.lastCases (motive := fun _ => K) (v i') (A i') j) i

@[simp] lemma border_castSucc_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i j : Fin r) : border A v u d i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] lemma border_castSucc_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (i : Fin r) : border A v u d i.castSucc (Fin.last r) = v i := by
  simp [border]

@[simp] lemma border_last_castSucc {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) (j : Fin r) : border A v u d (Fin.last r) j.castSucc = u j := by
  simp [border]

@[simp] lemma border_last_last {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K)
    (d : K) : border A v u d (Fin.last r) (Fin.last r) = d := by
  simp [border]

def borderEquiv (r : ℕ) :
    (Matrix (Fin r) (Fin r) K × (Fin r → K) × (Fin r → K) × K) ≃
      Matrix (Fin (r + 1)) (Fin (r + 1)) K where
  toFun x := border x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun C := (C.submatrix Fin.castSucc Fin.castSucc, fun i => C i.castSucc (Fin.last r),
    fun j => C (Fin.last r) j.castSucc, C (Fin.last r) (Fin.last r))
  left_inv x := by
    obtain ⟨A, v, u, d⟩ := x
    ext <;> simp
  right_inv C := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

lemma det_border {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    (border A v u d).det = (border A v u 0).det + d * A.det := by
  have hsub : ∀ (e : K) (g : Fin r → Fin (r + 1)),
      (border A v u e).submatrix Fin.castSucc g = (border A v u 0).submatrix Fin.castSucc g := by
    intro e g
    ext i k
    simp [border]
  rw [Matrix.det_succ_row _ (Fin.last r), Matrix.det_succ_row _ (Fin.last r),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hA : ∀ e : K, (border A v u e).submatrix Fin.castSucc Fin.castSucc = A := by
    intro e
    ext i k
    simp
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  simp only [border_last_castSucc, border_last_last, hpow, Fin.succAbove_last, hsub d, hA]
  ring

lemma lead_border_iff {r : ℕ} (A : Matrix (Fin r) (Fin r) K) (v u : Fin r → K) (d : K) :
    Lead (r + 1) (border A v u d) ↔ Lead r A ∧ (border A v u d).det ≠ 0 := by
  have hsmall : ∀ (j : ℕ) (hj : j ≤ r),
      (border A v u d).submatrix (Fin.castLE (hj.trans (Nat.le_succ r)))
        (Fin.castLE (hj.trans (Nat.le_succ r))) = A.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
    intro j hj
    ext i k
    change border A v u d (Fin.castLE hj i).castSucc (Fin.castLE hj k).castSucc = _
    exact border_castSucc_castSucc A v u d _ _
  have hfull : (border A v u d).submatrix (Fin.castLE (le_refl (r + 1)))
      (Fin.castLE (le_refl (r + 1))) = border A v u d := by
    ext i k
    rfl
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h j (hj.trans (Nat.le_succ r))
      rwa [hsmall j hj] at this
    · have := h (r + 1) le_rfl
      rwa [hfull] at this
  · rintro ⟨hA, hd⟩ j hj
    rcases Nat.lt_or_ge j (r + 1) with hlt | hge
    · have hj' : j ≤ r := Nat.lt_succ_iff.mp hlt
      have := hsmall j hj'
      rw [this]
      exact hA j hj'
    · obtain rfl : j = r + 1 := le_antisymm hj hge
      rw [hfull]
      exact hd

lemma det_ne_zero_of_lead {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (h : Lead r A) : A.det ≠ 0 := by
  have := h r le_rfl
  have hfull : A.submatrix (Fin.castLE (le_refl r)) (Fin.castLE (le_refl r)) = A := by
    ext i k
    rfl
  rwa [hfull] at this

noncomputable def leadSuccEquiv (r : ℕ) :
    {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} ≃
      {A : Matrix (Fin r) (Fin r) K // Lead r A} × (Fin r → K) × (Fin r → K) × {t : K // t ≠ 0} :=
  ((borderEquiv r).subtypeEquiv (p := fun x => Lead (r + 1) (borderEquiv r x))
      (fun _ => Iff.rfl)).symm.trans
  { toFun := fun x =>
      (⟨x.1.1, ((lead_border_iff _ _ _ _).mp x.2).1⟩, x.1.2.1, x.1.2.2.1,
        ⟨(border x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2).det, ((lead_border_iff _ _ _ _).mp x.2).2⟩)
    invFun := fun y =>
      ⟨(y.1.1, y.2.1, y.2.2.1, (y.2.2.2.1 - (border y.1.1 y.2.1 y.2.2.1 0).det) / y.1.1.det), by
        rw [show Lead (r + 1) (borderEquiv r _) ↔ _ from lead_border_iff _ _ _ _]
        refine ⟨y.1.2, ?_⟩
        rw [det_border, div_mul_cancel₀ _ (det_ne_zero_of_lead y.1.2)]
        simpa using y.2.2.2.2⟩
    left_inv := by
      rintro ⟨⟨A, v, u, d⟩, h⟩
      have hA := det_ne_zero_of_lead ((lead_border_iff A v u d).mp h).1
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      rw [det_border]
      field_simp
      ring
    right_inv := by
      rintro ⟨⟨A, hA⟩, v, u, ⟨t, ht⟩⟩
      have hA' := det_ne_zero_of_lead hA
      simp only [Prod.mk.injEq, Subtype.mk.injEq, true_and]
      rw [det_border, div_mul_cancel₀ _ hA']
      ring }

variable [Fintype K]

lemma card_lead_succ (r : ℕ) :
    Nat.card {C : Matrix (Fin (r + 1)) (Fin (r + 1)) K // Lead (r + 1) C} =
      Nat.card {A : Matrix (Fin r) (Fin r) K // Lead r A} *
        (Fintype.card K ^ r * (Fintype.card K ^ r * (Fintype.card K - 1))) := by
  classical
  rw [Nat.card_congr (leadSuccEquiv r), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_fun, Nat.card_congr (unitsEquivNeZero (G₀ := K)).symm, Nat.card_eq_fintype_card (α := Kˣ),
    Fintype.card_units, Nat.card_eq_fintype_card (α := K), Nat.card_eq_fintype_card (α := Fin r),
    Fintype.card_fin]

lemma card_lead_zero : Nat.card {C : Matrix (Fin 0) (Fin 0) K // Lead 0 C} = 1 := by
  classical
  have h : ∀ C : Matrix (Fin 0) (Fin 0) K, Lead 0 C := by
    intro C j hj
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h)]
  exact Nat.card_unique (α := Fin 0 → Fin 0 → K)

lemma card_lead (r : ℕ) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // Lead r C} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  induction r with
  | zero => simpa using card_lead_zero
  | succ r ih =>
    rw [card_lead_succ, ih]
    have h1 : (r + 1) ^ 2 - (r + 1) = r ^ 2 - r + r + r := by
      have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
      have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
      omega
    rw [h1, pow_add, pow_add, pow_succ]
    ring

end Formalism.FourierDecayAlt.P.Minors

theorem Formalism.FourierDecayAlt.P.leading_minors_count : Formalism.FourierDecayAlt.LeadingMinorsCount := by
  intro K _ _ r
  exact Formalism.FourierDecayAlt.P.Minors.card_lead r
