import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BracketIndepOfCofactors

open MvPolynomial Finset Formalism.BasicNotions Formalism.BasicNotions.DV

namespace GlobalTheory.FlagRankTwo

def gs {S : Type*} [CommRing S] (k : ℕ) (x y : S) : S :=
  ∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)

theorem gs_mul {S : Type*} [CommRing S] (k : ℕ) (x y : S) : gs k x y * (x - y) = x ^ k - y ^ k :=
  geom_sum₂_mul x y k

theorem gs_succ {S : Type*} [CommRing S] (k : ℕ) (a b : S) : gs (k+1) a b = a ^ k + b * gs k a b := by
  unfold gs
  simpa using geom_sum₂_succ_eq a b (n := k)

theorem key {S : Type*} [CommRing S] (k : ℕ) (a b c : S) : ∃ H : S,
    gs k a c - gs k a b = (c - b) * H ∧ gs k a c - gs k b c = (a - b) * H := by
  induction k with
  | zero => exact ⟨0, by simp [gs], by simp [gs]⟩
  | succ k ih =>
    obtain ⟨H, h1, h2⟩ := ih
    refine ⟨c * H + gs k a b, ?_, ?_⟩
    · rw [gs_succ, gs_succ]; linear_combination c * h1
    · rw [gs_succ, gs_succ]; linear_combination c * h2 - gs_mul k a b

theorem F_fac {S : Type*} [CommRing S] (k : ℕ) (y0 y1 y2 : S) : ∃ H : S,
    y0 ^ k + (y1 + y2) ^ k - y1 ^ k - (y0 + y2) ^ k = y2 * (y0 - y1) * H := by
  obtain ⟨H1, -, e1⟩ := key k (y1 + y2) (y0 + y2) y1
  obtain ⟨H2, e2, -⟩ := key k (y0 + y2) y0 y1
  refine ⟨-(H1 + H2), ?_⟩
  have f1 := gs_mul k (y1 + y2) y1
  have f0 := gs_mul k (y0 + y2) y0
  linear_combination -f1 + f0 + y2 * e1 + y2 * e2

theorem exists_sum_X_mul {S : Type*} [CommRing S] {n : ℕ} (p : MvPolynomial (Fin n) S)
    (hp : constantCoeff p = 0) : ∃ K : Fin n → MvPolynomial (Fin n) S, p = ∑ i, X i * K i := by
  have hmem : p ∈ Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) S)) := by
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    by_contra hcon
    push_neg at hcon
    have h0 : mo = 0 := by ext i; simpa using hcon i (Set.mem_univ i)
    subst h0
    rw [MvPolynomial.mem_support_iff] at hmo
    exact hmo (by rw [← hp]; rfl)
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
  exact ⟨c, by rw [← hc]; simp [mul_comm]⟩

end GlobalTheory.FlagRankTwo

namespace GlobalTheory.FlagRankTwo

theorem bracket_eq (Z : ITh)
    (hc : ∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a))
    {r : ℕ} (Dd : Fin r → Z.VDiv) (Q : Z.Ch) (G G' : Fin r → MvPolynomial (Fin r) Z.Ch)
    (h : ∑ i, X i * G i = ∑ i, X i * G' i) :
    ∑ i, Z.capDeg (Dd i) (aeval (fun j => Z.cD (Dd j)) (G i) * Q) =
      ∑ i, Z.capDeg (Dd i) (aeval (fun j => Z.cD (Dd j)) (G' i) * Q) := by
  have h0 : ∑ i, X i * (fun i => G i - G' i) i = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h, sub_self]
  obtain ⟨H, hanti, -, hG⟩ := GlobalTheory.koszul_relations_among_variables Z.Ch r (fun i => G i - G' i) h0
  set t : Fin r → Fin r → ℚ := fun i j =>
    Z.capDeg (Dd i) (Z.cD (Dd j) * (aeval (fun j => Z.cD (Dd j)) (H i j) * Q)) with ht
  have hterm : ∀ i, Z.capDeg (Dd i) (aeval (fun j => Z.cD (Dd j)) (G i) * Q) -
      Z.capDeg (Dd i) (aeval (fun j => Z.cD (Dd j)) (G' i) * Q) = ∑ j, t i j := by
    intro i
    rw [← map_sub, ← sub_mul, ← map_sub, hG i, map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.map_mul (aeval (fun j => Z.cD (Dd j))) (X j) (H i j), aeval_X, mul_assoc]
  have hsw : ∀ i j, t i j = - t j i := by
    intro i j
    simp only [ht]
    rw [hc, hanti i j, map_neg, neg_mul, mul_neg, map_neg]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  have hS : ∑ i, ∑ j, t i j = - ∑ i, ∑ j, t i j := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hsw i j
  linarith

end GlobalTheory.FlagRankTwo

namespace GlobalTheory.FlagRankTwo

theorem aeval_gs {n : ℕ} {S : Type*} [CommRing S] (f : Fin n → S) (k : ℕ) (x y : MvPolynomial (Fin n) S) :
    aeval f (gs k x y) = gs k (aeval f x) (aeval f y) := by
  simp [gs, map_sum, map_mul, map_pow]

theorem core (Z : ITh)
    (hc : ∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a))
    (k : ℕ) (Q l m z : Z.Ch) (a b V : Z.VDiv)
    (h4 : ∀ (D : Z.VDiv) (y : Z.Ch), Z.capDeg D ((z - Z.cD V) * ((l - Z.cD a) - (m - Z.cD b)) * y) = 0)
    (h5 : ∀ y : Z.Ch, Z.capDeg V ((l - m) * y) + Z.capDeg (a - b) ((z - Z.cD V) * y) = 0) :
    Z.capDeg a (gs k l (l - Z.cD a) * Q) + Z.capDeg (b + V) (gs k (m + z) ((m - Z.cD b) + (z - Z.cD V)) * Q) =
      Z.capDeg b (gs k m (m - Z.cD b) * Q) + Z.capDeg (a + V) (gs k (l + z) ((l - Z.cD a) + (z - Z.cD V)) * Q) := by
  obtain ⟨Hp, hHp⟩ := F_fac k (C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch)) (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch))
  obtain ⟨K, hK⟩ := exists_sum_X_mul ((C (constantCoeff Hp) : (MvPolynomial (Fin 3) Z.Ch)) - Hp) (by simp)
  have hFu : (C l : (MvPolynomial (Fin 3) Z.Ch)) ^ k + ((C m : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ^ k - (C m : (MvPolynomial (Fin 3) Z.Ch)) ^ k - ((C l : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ^ k = (C z : (MvPolynomial (Fin 3) Z.Ch)) * ((C l : (MvPolynomial (Fin 3) Z.Ch)) - (C m : (MvPolynomial (Fin 3) Z.Ch))) * C (constantCoeff Hp) := by
    simpa using congrArg (fun p => (C (constantCoeff p) : (MvPolynomial (Fin 3) Z.Ch))) hHp
  have I0 := gs_mul k (C l : (MvPolynomial (Fin 3) Z.Ch)) (C l - X 0 : (MvPolynomial (Fin 3) Z.Ch))
  have I1 := gs_mul k (C m : (MvPolynomial (Fin 3) Z.Ch)) (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch))
  have IA := gs_mul k ((C l : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)))
  have IB := gs_mul k ((C m : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C m - X 1 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)))
  have heq : ∑ i, X i * (![gs k (C l : (MvPolynomial (Fin 3) Z.Ch)) (C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) - gs k ((C l : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch))), gs k ((C m : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C m - X 1 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch))) - gs k (C m : (MvPolynomial (Fin 3) Z.Ch)) (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch)),
      gs k ((C m : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C m - X 1 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch))) - gs k ((C l : (MvPolynomial (Fin 3) Z.Ch)) + (C z : (MvPolynomial (Fin 3) Z.Ch))) ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)))] : Fin 3 → (MvPolynomial (Fin 3) Z.Ch)) i =
      ∑ i, X i * (![(C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * C (constantCoeff Hp) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) - (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch))) * K 0,
        -((C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * C (constantCoeff Hp)) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) - (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch))) * K 1,
        ((C l : (MvPolynomial (Fin 3) Z.Ch)) - (C m : (MvPolynomial (Fin 3) Z.Ch))) * C (constantCoeff Hp) + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) - (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch))) * K 2] : Fin 3 → (MvPolynomial (Fin 3) Z.Ch)) i := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [Fin.sum_univ_three] at hK
    linear_combination I0 + IB - I1 - IA + hFu - hHp + (C z - X 2 : (MvPolynomial (Fin 3) Z.Ch)) * ((C l - X 0 : (MvPolynomial (Fin 3) Z.Ch)) - (C m - X 1 : (MvPolynomial (Fin 3) Z.Ch))) * hK
  have hbr := bracket_eq Z hc ![a, b, V] Q _ _ heq
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, aeval_gs, map_add, map_sub, map_mul, map_neg, aeval_C, aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply] at hbr
  have e5 := h5 (constantCoeff Hp * Q)
  have e0 := h4 a (aeval (fun j => Z.cD (![a, b, V] j)) (K 0) * Q)
  have e1 := h4 b (aeval (fun j => Z.cD (![a, b, V] j)) (K 1) * Q)
  have e2 := h4 V (aeval (fun j => Z.cD (![a, b, V] j)) (K 2) * Q)
  generalize aeval (fun j => Z.cD (![a, b, V] j)) (K 0) = k0 at *
  generalize aeval (fun j => Z.cD (![a, b, V] j)) (K 1) = k1 at *
  generalize aeval (fun j => Z.cD (![a, b, V] j)) (K 2) = k2 at *
  clear h4 h5 heq hK hFu hHp I0 I1 IA IB
  generalize z - Z.cD V = z' at *
  generalize l - Z.cD a = l' at *
  generalize m - Z.cD b = m' at *
  generalize l' - m' = L' at *
  generalize l - m = L at *
  simp only [sub_mul, add_mul, neg_mul, map_add, map_sub, map_neg, LinearMap.add_apply,
    LinearMap.sub_apply, mul_assoc] at hbr e5 e0 e1 e2 ⊢
  linarith

theorem ck_eq_of_rank_two : ∀ (Z : ITh) (P P' : FPair Z 2) (k : ℕ) (Q : Z.Ch), (∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a)) → Z.c1 (P.x 0) + Z.c1 (P.x 1) = Z.c1 (P'.x 0) + Z.c1 (P'.x 1) → P.Dv 0 + P.Dv 1 = P'.Dv 0 + P'.Dv 1 → (∀ (D : Z.VDiv) (y : Z.Ch), Z.capDeg D ((Z.c1 (P'.x' 1) - Z.c1 (P.x' 0)) * (Z.c1 (P.x' 0) - Z.c1 (P'.x' 0)) * y) = 0) → (∀ y : Z.Ch, Z.capDeg (P.Dv 1 - P'.Dv 0) ((Z.c1 (P.x 0) - Z.c1 (P'.x 0)) * y) + Z.capDeg (P.Dv 0 - P'.Dv 0) ((Z.c1 (P'.x' 1) - Z.c1 (P.x' 0)) * y) = 0) → ck P k Q = ck P' k Q := by
  intro Z P P' k Q hc h2 h3 h4 h5
  obtain ⟨z, hz⟩ : ∃ z, Z.c1 (P'.x 1) = Z.c1 (P.x 0) + z := ⟨Z.c1 (P'.x 1) - Z.c1 (P.x 0), by ring⟩
  obtain ⟨V, hV⟩ : ∃ V, P.Dv 1 = P'.Dv 0 + V := ⟨P.Dv 1 - P'.Dv 0, by abel⟩
  have hz' : Z.c1 (P.x 1) = Z.c1 (P'.x 0) + z := by linear_combination h2 + hz
  have hV' : P'.Dv 1 = P.Dv 0 + V := by
    have : P'.Dv 1 = P.Dv 0 + P.Dv 1 - P'.Dv 0 := by rw [h3]; abel
    rw [this, hV]; abel
  have a0 := P.hx 0
  have b0 := P'.hx 0
  have a1 : Z.c1 (P.x' 1) = (Z.c1 (P'.x 0) - Z.cD (P'.Dv 0)) + (z - Z.cD V) := by
    rw [P.hx 1, hz', hV, map_add]; ring
  have b1 : Z.c1 (P'.x' 1) = (Z.c1 (P.x 0) - Z.cD (P.Dv 0)) + (z - Z.cD V) := by
    rw [P'.hx 1, hz, hV', map_add]; ring
  have hzz : Z.c1 (P'.x' 1) - Z.c1 (P.x' 0) = z - Z.cD V := by rw [b1, a0]; ring
  have hVV : P.Dv 1 - P'.Dv 0 = V := by rw [hV]; abel
  rw [hzz, a0, b0] at h4
  rw [hzz, hVV] at h5
  have := core Z hc k Q _ _ z _ _ V h4 h5
  simp only [ck, Fin.sum_univ_two]
  rw [a0, b0, a1, b1, hz, hz', hV, hV']
  exact this

end GlobalTheory.FlagRankTwo
