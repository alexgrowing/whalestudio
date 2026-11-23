import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

def rel (E : Fin n → Fin n → A) (a b c d : Fin n) : A :=
  E a b * E c d - E c d * E a b - ((if b = c then E a d else 0) - (if d = a then E c b else 0))

theorem glRel_iff (E : Fin n → Fin n → A) : GlRel E ↔ ∀ a b c d, rel E a b c d = 0 := by
  unfold GlRel rel
  constructor
  · intro h a b c d; rw [h a b c d, sub_self]
  · intro h a b c d; exact sub_eq_zero.mp (h a b c d)

theorem two_formal (E : Fin n → Fin n → A) (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = rel E p c q d + rel E p d q c := by
  obtain rfl : y = x - 1 := by linear_combination -hxy
  unfold rel
  simp only [eq_comm (a := c) (b := q), eq_comm (a := d) (b := p), eq_comm (a := d) (b := q),
    eq_comm (a := c) (b := p)]
  rw [ite_zero_eq_ite_smul (q = c) (E p d), ite_zero_eq_ite_smul (p = d) (E q c), ite_zero_eq_ite_smul (q = d) (E p c), ite_zero_eq_ite_smul (p = c) (E q d)]
  simp only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [ite_zero_eq_mul_ite (p = c) x, ite_zero_eq_mul_ite (q = d) (x - 1), ite_zero_eq_mul_ite (q = c) x, ite_zero_eq_mul_ite (p = d) (x - 1),
    ite_zero_eq_mul_ite (p = d) x, ite_zero_eq_mul_ite (q = c) (x - 1), ite_zero_eq_mul_ite (q = d) x, ite_zero_eq_mul_ite (p = c) (x - 1)]
  module

theorem four_formal {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod =
      ((List.ofFn f₁).take i).prod * (f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
        + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩) *
        ((List.ofFn f₁).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi, prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)), sandwich_alternating_sum]

def fac (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : Fin t → A :=
  fun k => Tm E (u - (k : ℂ)) (a (σ k)) (b k)

def Lt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).take (i : ℕ)).prod

def Rt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).drop ((i : ℕ) + 2)).prod

def Md (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) : A :=
  rel E (a (σ i.castSucc)) (b i.castSucc) (a (σ i.succ)) (b i.succ) +
    rel E (a (σ i.castSucc)) (b i.succ) (a (σ i.succ)) (b i.castSucc)

theorem key_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ)
    (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) =
      Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold exchangeTwo_self_eq_one Lt Rt
  rw [four_formal _ _ _ _ (i : ℕ) (by omega)]
  · congr 2
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Md]
    exact two_formal E _ _ (by simp) _ _ _ _
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]

theorem adj_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    (2 : ℂ) • (qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u + qminor E a b u) =
      ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → A := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : A) * (exchangeTwo_self_eq_one E a (b ∘ s) u σ + exchangeTwo_self_eq_one E a b u σ) with hG
  have hsum : qminor E a (b ∘ s) u + qminor E a b u = ∑ σ, G σ := by
    rw [quantumMinor_eq_sum_term, quantumMinor_eq_sum_term, ← Finset.sum_add_distrib]
    simp only [hG, mul_add]
  have hre : ∑ σ, G (σ * s) = ∑ σ, G σ := Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ σ, G σ + G (σ * s) =
      ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
    intro σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg]
    have k := key_formal E a b i u σ
    rw [← hs_def] at k
    rw [← k]
    noncomm_ring
  rw [hsum, two_smul, ← Finset.sum_congr rfl (fun σ _ => hpair σ), Finset.sum_add_distrib, hre]

def Ead (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : A :=
  ∑ a, ∑ b, (P a c * Q d b) • E a b

theorem Tm_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) (v : ℂ) (c d : Fin n) :
    Tm (Ead E P Q) v c d = ∑ a, ∑ b, (P a c * Q d b) • Tm E v a b := by
  have h1 : ∀ a, ∑ b, (P a c * Q d b) • (if a = b then algebraMap ℂ A v else 0) =
      (P a c * Q d a) • algebraMap ℂ A v := by
    intro a; simp [smul_ite]
  have h2 : ∑ a, P a c * Q d a = if c = d then 1 else 0 := by
    have := congrFun (congrFun hQP d) c
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ a, P a c * Q d a) = ∑ a, Q d a * P a c from Finset.sum_congr rfl fun a _ => mul_comm _ _, this]
    simp [eq_comm]
  unfold Tm Ead
  simp only [smul_add, Finset.sum_add_distrib, h1]
  rw [← Finset.sum_smul, h2]
  split_ifs <;> simp

theorem prod_expand {X : Type*} [Fintype X] :
    ∀ (t : ℕ) (c : Fin t → X → ℂ) (B : Fin t → X → A),
      (List.ofFn fun j => ∑ x, c j x • B j x).prod =
        ∑ φ : Fin t → X, (∏ j, c j (φ j)) • (List.ofFn fun j => B j (φ j)).prod := by
  intro t
  induction t with
  | zero => intro c B; simp
  | succ t ih =>
    intro c B
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => B j.succ), Finset.sum_mul]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => X).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ,
      List.prod_cons, smul_mul_smul_comm]

theorem rowsum_det {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P (α j) (e (σ j)) =
      (Matrix.of fun i j : Fin t => P (α i) (e j)).det := by
  rw [Matrix.det_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin t))) _ _ (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)

theorem det_rows_perm {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (γ : Equiv.Perm (Fin t)) :
    (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det = ((Equiv.Perm.sign γ : ℤ) : ℂ) * P.det := by
  have : (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)) = (P.submatrix e e).submatrix γ id := by
    ext i j; simp
  rw [this, Matrix.det_permute, Matrix.det_submatrix_equiv_self]

theorem det_rows_zero {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n)
    (hα : ¬ Function.Injective α) : (Matrix.of fun i j : Fin t => P (α i) (e j)).det = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, i', h, hne⟩ := hα
  exact Matrix.det_zero_of_row_eq hne (by funext j; simp [h])

theorem sum_inj {M : Type*} [AddCommMonoid M] {t : ℕ} (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ α, ¬ Function.Injective α → F α = 0) :
    ∑ α, F α = ∑ γ : Equiv.Perm (Fin t), F (e ∘ γ) := by
  classical
  have himg : ∑ α ∈ (Finset.univ.image fun γ : Equiv.Perm (Fin t) => (e ∘ γ : Fin t → Fin n)), F α = ∑ α, F α := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro α _ hα
    apply hF
    intro hinj
    apply hα
    have hi : Function.Injective (e.symm ∘ α) := e.symm.injective.comp hinj
    have hs : Function.Surjective (e.symm ∘ α) := Finite.injective_iff_surjective.mp hi
    refine Finset.mem_image.mpr ⟨Equiv.ofBijective _ ⟨hi, hs⟩, Finset.mem_univ _, ?_⟩
    funext j
    show e ((e.symm ∘ α) j) = α j
    simp
  rw [← himg, Finset.sum_image]
  intro γ₁ _ γ₂ _ h
  exact Equiv.ext fun j => by have := congrFun h j; simpa using this

theorem qminor_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) {t : ℕ}
    (e : Fin t ≃ Fin n) (u : ℂ) :
    qminor (Ead E P Q) e e u = P.det • ∑ β : Fin t → Fin n, (∏ j, Q (e j) (β j)) • qminor E e β u := by
  have step1 : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod =
        ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro σ
    calc (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod
        = (List.ofFn fun j : Fin t => ∑ x : Fin n × Fin n,
            (P x.1 (e (σ j)) * Q (e j) x.2) • Tm E (u - (j : ℂ)) x.1 x.2).prod := by
          simp only [Tm_Ead E hQP, ← Finset.sum_product', Finset.univ_product_univ]
      _ = ∑ φ : Fin t → Fin n × Fin n, (∏ j, (P (φ j).1 (e (σ j)) * Q (e j) (φ j).2)) •
            (List.ofFn fun j => Tm E (u - (j : ℂ)) (φ j).1 (φ j).2).prod :=
          by exact prod_expand (X := Fin n × Fin n) t _ _
      _ = _ := by
          rw [← (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type,
            Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          simp [Equiv.arrowProdEquivProdArrow, Finset.prod_mul_distrib]
  have inner : ∀ β α : Fin t → Fin n,
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) =
      ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro β α
    rw [← rowsum_det P e α, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show ((Equiv.Perm.sign σ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
      ← Algebra.smul_def, smul_smul, mul_assoc]
  calc qminor (Ead E P Q) e e u
      = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        unfold qminor; simp only [step1]
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n, ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
          (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_comm
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        simp only [inner]
    _ = ∑ β : Fin t → Fin n, ∑ γ : Equiv.Perm (Fin t),
          ((Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (e (γ k)) (β k)).prod := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [sum_inj e _ (fun α hα => by rw [det_rows_zero P e α hα, zero_mul, zero_smul])]
        rfl
    _ = ∑ β : Fin t → Fin n, P.det • ((∏ j, Q (e j) (β j)) • qminor E e β u) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        unfold qminor
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [det_rows_perm P e γ,
          show ((Equiv.Perm.sign γ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign γ : ℤ) : ℂ) by simp,
          ← Algebra.smul_def, smul_smul, smul_smul]
        congr 1
        ring
    _ = _ := by rw [Finset.smul_sum]

end Formalism.FourierDecayAlt.P.JFxE
