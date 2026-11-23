import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32

set_option linter.unusedVariables false

namespace MassDataIdxStIm

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hoff : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card = n * (n - 1) := by
    have h1 : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
        (Finset.univ : Finset (Fin n)).offDiag := by
      ext p
      simp [Finset.mem_offDiag]
    rw [h1, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.mul_sub_one]
  have hsplit : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)) ∪
        (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      exact lt_or_gt_of_ne h
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
  have hdisj : Disjoint (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter] at hp hq
    exact lt_asymm hp.2 hq.2
  have hswap : (Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)).card =
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact hp
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hq ⊢
      exact hq
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap] at hoff
  generalize n * (n - 1) = X at hoff ⊢
  omega

theorem card_matrix (m n K : Type) [Finite m] [Finite n] :
    Nat.card (Matrix m n K) = Nat.card K ^ (Nat.card m * Nat.card n) := by
  show Nat.card (m → n → K) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.mul_comm (Nat.card n) (Nat.card m)]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv (A := K) n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

noncomputable def glEquiv (n : ℕ) : GL (Fin n) A ≃ {h : Matrix (Fin n) (Fin n) A // IsUnit h.det} where
  toFun g := ⟨g.1, (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit⟩
  invFun h := Matrix.GeneralLinearGroup.mk'' h.1 h.2
  left_inv g := Units.ext rfl
  right_inv h := rfl

variable {r k : ℕ}

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
theorem block11_of_blocks : b11 (mk a b c m e f) = a := by
  first
    | rfl
    | (ext i j; simp [mk, b11])
theorem block12_of_blocks : b12 (mk a b c m e f) = b := by
  first
    | rfl
    | (ext i j; simp [mk, b12])
theorem block13_of_blocks : b13 (mk a b c m e f) = c := by
  first
    | rfl
    | (ext i j; simp [mk, b13])
theorem block21_of_blocks : b21 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b21])
theorem block22_of_blocks : b22 (mk a b c m e f) = m := by
  first
    | rfl
    | (ext i j; simp [mk, b22])
theorem block23_of_blocks : b23 (mk a b c m e f) = e := by
  first
    | rfl
    | (ext i j; simp [mk, b23])
theorem block31_of_blocks : b31 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b31])
theorem block32_of_blocks : b32 (mk a b c m e f) = 0 := by
  first
    | rfl
    | (ext i j; simp [mk, b32])
theorem block33_of_blocks : b33 (mk a b c m e f) = f := by
  first
    | rfl
    | (ext i j; simp [mk, b33])
end mk

def parMap (P : Matrix (Fin k) (Fin k) A → Prop) :
    ({a : Matrix (Fin r) (Fin r) A // IsUpUni a} × {f : Matrix (Fin r) (Fin r) A // IsUpUni f} ×
      {h : Matrix (Fin k) (Fin k) A // P h} × Matrix (Fin r) (Mid k) A × Matrix (Fin r) (Fin r) A ×
      Matrix (Mid k) (Fin r) A) → {x : Matrix (Idx r k) (Idx r k) A // Par P x} :=
  fun t => ⟨mk t.1.1 t.2.2.2.1 t.2.2.2.2.1 (midEmb t.2.2.1.1) t.2.2.2.2.2 t.2.1.1,
    by rw [block11_of_blocks]; exact t.1.2, by rw [block33_of_blocks]; exact t.2.1.2, block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..,
    t.2.2.1.1, t.2.2.1.2, block22_of_blocks ..⟩

theorem parMap_bij (P : Matrix (Fin k) (Fin k) A → Prop) : Function.Bijective (parMap (r := r) P) := by
  constructor
  · rintro ⟨⟨a1, ha1⟩, ⟨f1, hf1⟩, ⟨h1, hh1⟩, b1, c1, e1⟩ ⟨⟨a2, ha2⟩, ⟨f2, hf2⟩, ⟨h2, hh2⟩, b2, c2, e2⟩ heq
    have hx := congrArg Subtype.val heq
    change mk a1 b1 c1 (midEmb h1) e1 f1 = mk a2 b2 c2 (midEmb h2) e2 f2 at hx
    have ea := congrArg b11 hx
    have eb := congrArg b12 hx
    have ec := congrArg b13 hx
    have em := congrArg b22 hx
    have ee := congrArg b23 hx
    have ef := congrArg b33 hx
    rw [block11_of_blocks, block11_of_blocks] at ea
    rw [block12_of_blocks, block12_of_blocks] at eb
    rw [block13_of_blocks, block13_of_blocks] at ec
    rw [block22_of_blocks, block22_of_blocks] at em
    rw [block23_of_blocks, block23_of_blocks] at ee
    rw [block33_of_blocks, block33_of_blocks] at ef
    have eh : h1 = h2 := by
      have := congrArg Matrix.toBlocks₁₁ em
      simpa [midEmb] using this
    subst ea eb ec ee ef eh
    rfl
  · rintro ⟨x, h11, h33, h21, h31, h32, h, hP, h22⟩
    refine ⟨(⟨b11 x, h11⟩, ⟨b33 x, h33⟩, ⟨h, hP⟩, b12 x, b13 x, b23 x), ?_⟩
    apply Subtype.ext
    change mk (b11 x) (b12 x) (b13 x) (midEmb h) (b23 x) (b33 x) = x
    have z21 : ∀ i j, x (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := fun i j => by
      simpa [b21] using congrFun (congrFun h21 i) j
    have z31 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := fun i j => by
      simpa [b31] using congrFun (congrFun h31 i) j
    have z32 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := fun i j => by
      simpa [b32] using congrFun (congrFun h32 i) j
    rw [← h22]
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [mk, b11, b12, b13, b22, b23, b33, z21, z31, z32]

theorem card_par (K : Type) [Field K] [Fintype K] (r k : ℕ) (P : Matrix (Fin k) (Fin k) K → Prop) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par P x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // P h} *
        Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  have hM : Nat.card (Mid k) = k + 1 := by
    unfold Mid
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [← Nat.card_congr (Equiv.ofBijective _ (parMap_bij (r := r) P))]
  simp only [Nat.card_prod, card_uni, card_matrix, hM, Nat.card_fin]
  rw [Nat.card_eq_fintype_card (α := K)]
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self r
  rw [ht, show (t + t) / 2 = t by omega]
  ring

theorem card_isN (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
  have e : {x : Matrix (Idx r k) (Idx r k) K // IsN x} ≃
      {x : Matrix (Idx r k) (Idx r k) K // Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x} :=
    Equiv.subtypeEquivRight (fun x => by
      unfold IsN Par
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3]; simp [midEmb]⟩
      · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
        exact ⟨h1, h2, by rw [h3]; simp [midEmb], h4, h5, h6⟩)
  have hone : Nat.card {h : Matrix (Fin k) (Fin k) K // h = 1} = 1 := by
    first
      | exact Nat.card_unique
      | simp
  rw [Nat.card_congr e, card_par, hone, one_mul]

end Count

end MassDataIdxStIm
