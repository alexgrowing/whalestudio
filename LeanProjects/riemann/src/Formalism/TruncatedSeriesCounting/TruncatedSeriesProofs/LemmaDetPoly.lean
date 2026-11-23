import Formalism.TruncatedSeriesCounting.LemmaDetPoly

open Finset Classical Polynomial

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore

variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]

def polyS (S : Subring R) : Subring R[X] where
  carrier := {p | ∀ k, p.coeff k ∈ S}
  mul_mem' := by
    intro p q hp hq k
    show (p * q).coeff k ∈ S
    rw [Polynomial.coeff_mul]
    exact Subring.sum_mem _ (fun x _ => S.mul_mem (hp _) (hq _))
  one_mem' := by
    intro k
    show (1 : R[X]).coeff k ∈ S
    rw [Polynomial.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' := by
    intro p q hp hq k
    show (p + q).coeff k ∈ S
    rw [Polynomial.coeff_add]; exact S.add_mem (hp k) (hq k)
  zero_mem' := by intro k; show (0 : R[X]).coeff k ∈ S; simp [S.zero_mem]
  neg_mem' := by
    intro p hp k
    show (-p).coeff k ∈ S
    rw [Polynomial.coeff_neg]; exact S.neg_mem (hp k)

lemma C_mem_polyS {S : Subring R} {c : R} (hc : c ∈ S) : C c ∈ polyS S := by
  intro k
  show (C c).coeff k ∈ S
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact S.zero_mem

lemma X_mem_polyS {S : Subring R} : (X : R[X]) ∈ polyS S := by
  intro k
  show (X : R[X]).coeff k ∈ S
  rw [Polynomial.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

lemma comp_mem_polyS {S : Subring R} {p q : R[X]} (hp : p ∈ polyS S) (hq : q ∈ polyS S) :
    p.comp q ∈ polyS S := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum]
  exact Subring.sum_mem _ (fun e _ => (polyS S).mul_mem (C_mem_polyS (hp e)) ((polyS S).pow_mem hq e))

def term (ρ : G →* Matrix n n R) (L : R × ℕ × G) : Matrix n n R[X] :=
  (C L.1 * X ^ L.2.1) • (C : R →+* R[X]).mapMatrix (ρ L.2.2)

def F (ρ : G →* Matrix n n R) (l : List (R × ℕ × G)) : R[X] :=
  Matrix.det (1 - (l.map (term ρ)).sum)

def newL (L0 L : R × ℕ × G) (k : ℕ) : R × ℕ × G :=
  (L0.1 ^ k * L.1, k * L0.2.1 + L.2.1, L0.2.2 ^ k * L.2.2)

lemma term_newL (ρ : G →* Matrix n n R) (L0 L : R × ℕ × G) (k : ℕ) :
    term ρ (newL L0 L k) = term ρ L0 ^ k * term ρ L := by
  simp only [term, newL, map_mul, map_pow, _root_.smul_pow, smul_mul_smul_comm]
  congr 1
  ring

lemma F_perm (ρ : G →* Matrix n n R) {l l' : List (R × ℕ × G)} (h : l.Perm l') : F ρ l = F ρ l' := by
  unfold F
  rw [(h.map _).sum_eq]

lemma charpoly_comp (ρ : G →* Matrix n n R) (L : R × ℕ × G) :
    Matrix.det (1 - term ρ L) = (Matrix.charpolyRev (ρ L.2.2)).comp (C L.1 * X ^ L.2.1) := by
  unfold Matrix.charpolyRev term
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [h] <;> ring

section Trunc

variable (N : ℕ)

abbrev piN : R[X] →+* R[X] ⧸ Ideal.span {(X : R[X]) ^ (N + 1)} := Ideal.Quotient.mk _

lemma piN_eq_zero {c : R} {d : ℕ} (hd : N + 1 ≤ d) : piN N (C c * X ^ d) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact Dvd.dvd.mul_left (pow_dvd_pow X hd) _

lemma mapMatrix_smul_zero {a : R[X]} (ha : piN N a = 0) (M : Matrix n n R[X]) :
    (piN N).mapMatrix (a • M) = 0 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, ha]

lemma geom_list {A : Type*} [Ring A] (x : A) (N : ℕ) :
    (1 - x) * (1 + ((List.range N).map (fun k => x ^ (k + 1))).sum) = 1 - x ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← add_assoc, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel

lemma alg_identity {A : Type*} [Ring A] (x : A) (N : ℕ) (hx : x ^ (N + 1) = 0) (ys : List A) :
    (1 - x) * (1 - (ys.sum + (ys.map (fun y => ((List.range N).map (fun k => x ^ (k + 1) * y)).sum)).sum)) =
      1 - (x + ys.sum) := by
  have h1 : (ys.map (fun y => ((List.range N).map (fun k => x ^ (k + 1) * y)).sum)).sum =
      ((List.range N).map (fun k => x ^ (k + 1))).sum * ys.sum := by
    simp only [List.sum_map_mul_right]
    rw [List.sum_map_mul_left, List.map_id']
  rw [h1]
  have hg := geom_list x N
  rw [hx, sub_zero] at hg
  calc (1 - x) * (1 - (ys.sum + ((List.range N).map (fun k => x ^ (k + 1))).sum * ys.sum))
      = (1 - x) - ((1 - x) * (1 + ((List.range N).map (fun k => x ^ (k + 1))).sum)) * ys.sum := by
        noncomm_ring
    _ = 1 - (x + ys.sum) := by
        rw [hg]
        noncomm_ring

lemma sum_flat {α A : Type*} [AddCommMonoid A] (f : α → A) (h : α → List α) (l : List α) :
    ((l.flatMap h).map f).sum = (l.map (fun a => ((h a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

def elim (L0 : R × ℕ × G) (rest : List (R × ℕ × G)) : List (R × ℕ × G) :=
  rest ++ rest.flatMap (fun L => (List.range N).map (fun k => newL L0 L (k + 1)))

lemma key (ρ : G →* Matrix n n R) (L0 : R × ℕ × G) (h0 : 1 ≤ L0.2.1) (rest : List (R × ℕ × G)) :
    piN N (F ρ (L0 :: rest)) = piN N (Matrix.det (1 - term ρ L0)) * piN N (F ρ (elim N L0 rest)) := by
  simp only [F, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  set φ := (piN (R := R) N).mapMatrix (m := n)
  have hx : (φ (term ρ L0)) ^ (N + 1) = 0 := by
    rw [← map_pow, term, _root_.smul_pow, mul_pow, ← pow_mul, ← map_pow]
    exact mapMatrix_smul_zero N (piN_eq_zero N (by nlinarith)) _
  have hnew : ∀ L k, φ (term ρ (newL L0 L (k + 1))) = φ (term ρ L0) ^ (k + 1) * φ (term ρ L) := by
    intro L k
    rw [term_newL, map_mul, map_pow]
  simp only [map_sub, map_one, map_add, map_list_sum, List.map_cons, List.sum_cons, elim,
    List.map_append, List.sum_append, sum_flat, List.map_map]
  rw [← alg_identity (φ (term ρ L0)) N hx]
  congr 3
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro L _
  simp only [Function.comp_apply]
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact (hnew L k).symm

variable {S : Subring R}

abbrev SQ (S : Subring R) : Subring (R[X] ⧸ Ideal.span {(X : R[X]) ^ (N + 1)}) :=
  (polyS S).map (piN N)

lemma base (ρ : G →* Matrix n n R) (l : List (R × ℕ × G)) (hl : ∀ L ∈ l, N + 1 ≤ L.2.1) :
    piN N (F ρ l) = 1 := by
  unfold F
  rw [RingHom.map_det, map_sub, map_one, map_list_sum, List.map_map]
  have h0 : (l.map ((piN N).mapMatrix ∘ term ρ)).sum = 0 := by
    apply List.sum_eq_zero
    intro M hM
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hM
    exact mapMatrix_smul_zero N (piN_eq_zero N (hl L hL)) _
  rw [h0, sub_zero, Matrix.det_one]

lemma letter_mem (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (L : R × ℕ × G) (hc : L.1 ∈ S) : piN N (Matrix.det (1 - term ρ L)) ∈ SQ N S := by
  rw [charpoly_comp]
  exact ⟨_, comp_mem_polyS (fun k => hS _ k)
    ((polyS S).mul_mem (C_mem_polyS hc) ((polyS S).pow_mem X_mem_polyS _)), rfl⟩

def Valid (S : Subring R) (D : ℕ) (l : List (R × ℕ × G)) : Prop := ∀ L ∈ l, L.1 ∈ S ∧ D ≤ L.2.1

lemma stepD (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (D : ℕ) (hD : 1 ≤ D) (ih : ∀ l, Valid S (D + 1) l → piN N (F ρ l) ∈ SQ N S) :
    ∀ c (l : List (R × ℕ × G)), Valid S D l → l.countP (fun L => L.2.1 = D) = c →
      piN N (F ρ l) ∈ SQ N S := by
  intro c
  induction c with
  | zero =>
    intro l hl hc
    apply ih
    intro L hL
    refine ⟨(hl L hL).1, ?_⟩
    have h1 := (hl L hL).2
    have h2 : ¬ (L.2.1 = D) := by
      have := List.countP_eq_zero.1 hc L hL
      simpa using this
    omega
  | succ c ihc =>
    intro l hl hc
    obtain ⟨L0, hL0, hd0⟩ : ∃ L0 ∈ l, L0.2.1 = D := by
      have : 0 < l.countP (fun L => L.2.1 = D) := by omega
      obtain ⟨a, ha, hpa⟩ := List.countP_pos_iff.1 this
      exact ⟨a, ha, by simpa using hpa⟩
    have hperm := List.perm_cons_erase hL0
    rw [F_perm ρ hperm, key N ρ L0 (by omega) _]
    refine (SQ N S).mul_mem (letter_mem N ρ hS L0 (hl L0 hL0).1) ?_
    apply ihc
    · intro L hL
      simp only [elim, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hL
      rcases hL with hL | ⟨L', hL', k, hk, rfl⟩
      · exact hl L (List.mem_of_mem_erase hL)
      · have h' := hl L' (List.mem_of_mem_erase hL')
        refine ⟨S.mul_mem (S.pow_mem (hl L0 hL0).1 _) h'.1, ?_⟩
        simp only [newL]
        have := h'.2
        omega
    · have hc' := hperm.countP_eq (fun L => L.2.1 = D)
      rw [List.countP_cons_of_pos (by simpa using hd0)] at hc'
      rw [elim, List.countP_append]
      have hz : (List.flatMap (fun L => (List.range N).map (fun k => newL L0 L (k + 1)))
          (l.erase L0)).countP (fun L => L.2.1 = D) = 0 := by
        rw [List.countP_eq_zero]
        intro L hL
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hL
        obtain ⟨L', hL', k, hk, rfl⟩ := hL
        have h' := hl L' (List.mem_of_mem_erase hL')
        have hm : L0.2.1 ≤ (k + 1) * L0.2.1 := Nat.le_mul_of_pos_left L0.2.1 (by omega)
        have := h'.2
        intro hc2
        have hc3 := of_decide_eq_true hc2
        simp only [newL] at hc3
        omega
      omega

lemma allD (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S) :
    ∀ j D, 1 ≤ D → N + 1 ≤ D + j → ∀ l : List (R × ℕ × G), Valid S D l → piN N (F ρ l) ∈ SQ N S := by
  intro j
  induction j with
  | zero =>
    intro D hD hj l hl
    rw [base N ρ l (fun L hL => by have := (hl L hL).2; omega)]
    exact (SQ N S).one_mem
  | succ j ih =>
    intro D hD hj l hl
    exact stepD N ρ hS D hD (fun l' hl' => ih (D + 1) (by omega) (by omega) l' hl') _ l hl rfl

end Trunc

theorem core {S : Subring R} (ρ : G →* Matrix n n R)
    (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (l : List (R × ℕ × G)) (hl : ∀ L ∈ l, L.1 ∈ S ∧ 1 ≤ L.2.1) (k : ℕ) : (F ρ l).coeff k ∈ S := by
  have h := allD k ρ hS (k + 1) 1 le_rfl (by omega) l hl
  obtain ⟨q, hq, hqe⟩ := Subring.mem_map.1 h
  have hmem : F ρ l - q ∈ Ideal.span {(X : R[X]) ^ (k + 1)} := by
    rw [← Ideal.Quotient.eq]; exact hqe.symm
  obtain ⟨h', hh'⟩ := Ideal.mem_span_singleton'.1 hmem
  have e : (F ρ l - q).coeff k = 0 := by
    rw [← hh', Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  rw [Polynomial.coeff_sub, sub_eq_zero] at e
  rw [e]
  exact hq k

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp

open DetPolyCore

section

variable {O K Xs : Type*} [CommRing O] [CommRing K] [Algebra O K]

def MainNotions (T : Subalgebra O (Xs → O)) : Subring (Xs → K) where
  carrier := {f | FromT T f}
  mul_mem' := by
    rintro f g ⟨t, ht, hf⟩ ⟨u, hu, hg⟩
    exact ⟨t * u, T.mul_mem ht hu, fun x => by simp [hf, hg]⟩
  one_mem' := ⟨1, T.one_mem, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨t, ht, hf⟩ ⟨u, hu, hg⟩
    exact ⟨t + u, T.add_mem ht hu, fun x => by simp [hf, hg]⟩
  zero_mem' := ⟨0, T.zero_mem, fun x => by simp⟩
  neg_mem' := by
    rintro f ⟨t, ht, hf⟩
    exact ⟨-t, T.neg_mem ht, fun x => by simp [hf]⟩

lemma mem_mainNotions_iff_fromT {T : Subalgebra O (Xs → O)} {f : Xs → K} : f ∈ MainNotions T ↔ FromT T f := Iff.rfl

def S1 (T : Subalgebra O (Xs → O)) (m : ℕ) : Subring (Xs → MvPolynomial (Fin m) K) where
  carrier := {f | ∀ α, (fun x => (f x).coeff α) ∈ MainNotions (K := K) T}
  mul_mem' := by
    intro f g hf hg α
    show (fun x => ((f * g) x).coeff α) ∈ MainNotions T
    simp only [Pi.mul_apply, MvPolynomial.coeff_mul]
    have key : ∀ s : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)),
        (fun x => ∑ p ∈ s, (f x).coeff p.1 * (g x).coeff p.2) ∈ MainNotions T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (fun x => ∑ p ∈ (∅ : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ))),
            (f x).coeff p.1 * (g x).coeff p.2) = 0 := by funext x; simp
        rw [e]; exact (MainNotions T).zero_mem
      | insert a s ha ih =>
        have e : (fun x => ∑ p ∈ insert a s, (f x).coeff p.1 * (g x).coeff p.2) =
            (fun x => (f x).coeff a.1) * (fun x => (g x).coeff a.2) +
              (fun x => ∑ p ∈ s, (f x).coeff p.1 * (g x).coeff p.2) := by
          funext x; simp [Finset.sum_insert ha]
        rw [e]; exact (MainNotions T).add_mem ((MainNotions T).mul_mem (hf _) (hg _)) ih
    exact key _
  one_mem' := by
    intro α
    show (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) ∈ MainNotions T
    by_cases h : (0 : Fin m →₀ ℕ) = α
    · have e : (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 1 := by
        funext x; simp [MvPolynomial.coeff_one, h]
      rw [e]; exact (MainNotions T).one_mem
    · have e : (fun x => ((1 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 0 := by
        funext x; simp [MvPolynomial.coeff_one, h]
      rw [e]; exact (MainNotions T).zero_mem
  add_mem' := by
    intro f g hf hg α
    have e : (fun x => ((f + g) x).coeff α) = (fun x => (f x).coeff α) + (fun x => (g x).coeff α) := by
      funext x; simp
    show (fun x => ((f + g) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).add_mem (hf α) (hg α)
  zero_mem' := by
    intro α
    have e : (fun x => ((0 : Xs → MvPolynomial (Fin m) K) x).coeff α) = 0 := by funext x; simp
    show (fun x => ((0 : Xs → MvPolynomial (Fin m) K) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).zero_mem
  neg_mem' := by
    intro f hf α
    have e : (fun x => ((-f) x).coeff α) = -(fun x => (f x).coeff α) := by funext x; simp
    show (fun x => ((-f) x).coeff α) ∈ MainNotions T
    rw [e]; exact (MainNotions T).neg_mem (hf α)

lemma S1_mem_OmF {T : Subalgebra O (Xs → O)} {m : ℕ} {f : Xs → MvPolynomial (Fin m) K} :
    f ∈ S1 T m ↔ ∀ α, FromT T (fun x => (f x).coeff α) := Iff.rfl

end

section

variable {K Xs G : Type*} [CommRing K] [Monoid G] {n : Type} [Fintype n] [DecidableEq n]

def rho (r : G →* (Xs → Matrix n n K)) (m : ℕ) : G →* Matrix n n (Xs → MvPolynomial (Fin m) K) where
  toFun g := Matrix.of fun i j x => MvPolynomial.C (r g x i j)
  map_one' := by
    refine Matrix.ext fun i j => funext fun x => ?_
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' := by
    intro g h
    refine Matrix.ext fun i j => funext fun x => ?_
    simp [Matrix.mul_apply, Finset.sum_apply]

lemma charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix n n A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [h]

lemma det_eq_coeff {A : Type*} [CommRing A] (M : Matrix n n A) :
    M.det = (-1) ^ Fintype.card n * (Matrix.charpolyRev M).coeff (Fintype.card n) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le le_rfl, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff]

lemma F_eq {R : Type*} [CommRing R] (ρ : G →* Matrix n n R) (l : List (R × ℕ × G))
    (hl : ∀ L ∈ l, L.2.1 = 1) :
    (l.map (term ρ)).sum = (Polynomial.X : Polynomial R) • ((l.map (fun L => L.1 • ρ L.2.2)).sum).map Polynomial.C := by
  induction l with
  | nil => simp
  | cons L l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      ih (fun L' h => hl L' (List.mem_cons_of_mem _ h))]
    have h1 := hl L List.mem_cons_self
    refine Matrix.ext fun i j => ?_
    simp [term, h1]
    ring

end

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

open DetPolyCore DetPolyApp

theorem det_poly_statement : LemmaDetPoly := by
  intro O K Xs G _ _ _ _ n _ _ T r hchar m a ha s
  choose sg c hc hae using ha
  let coefL : (Σ _ : Fin m, G) → Xs → MvPolynomial (Fin m) K :=
    fun p x => MvPolynomial.X p.1 * MvPolynomial.C (algebraMap O K (c p.1 p.2 x))
  have hcoef : ∀ p, coefL p ∈ S1 (K := K) T m := by
    intro p α
    show FromT T (fun x => (MvPolynomial.X p.1 * MvPolynomial.C (algebraMap O K (c p.1 p.2 x))).coeff α)
    simp only [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_C]
    by_cases h1 : p.1 ∈ α.support
    · by_cases h2 : (0 : Fin m →₀ ℕ) = α - Finsupp.single p.1 1
      · simp only [h1, h2, if_true]
        exact ⟨c p.1 p.2, hc p.1 p.2, fun x => rfl⟩
      · simp only [h1, h2, if_true, if_false]
        exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
    · simp only [h1, if_false]
      exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
  have hS : ∀ g k, (Matrix.charpolyRev (rho r m g)).coeff k ∈ S1 (K := K) T m := by
    intro g k α
    have e : ∀ x, (Matrix.charpolyRev (rho r m g)).coeff k x =
        MvPolynomial.C ((Matrix.charpolyRev (r g x)).coeff k) := by
      intro x
      have h1 : (Matrix.charpolyRev (rho r m g)).coeff k x =
          ((Matrix.charpolyRev (rho r m g)).map
            (Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x)).coeff k := by
        rw [Polynomial.coeff_map]; rfl
      rw [h1, charpolyRev_map,
        show (rho r m g).map (Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x) =
          (r g x).map MvPolynomial.C from Matrix.ext fun i j => rfl,
        ← charpolyRev_map, Polynomial.coeff_map]
    show FromT T (fun x => ((Matrix.charpolyRev (rho r m g)).coeff k x).coeff α)
    simp only [e, MvPolynomial.coeff_C]
    by_cases h : (0 : Fin m →₀ ℕ) = α
    · simp only [h, if_true]; exact hchar g k
    · simp only [h, if_false]; exact mem_mainNotions_iff_fromT.1 (MainNotions (K := K) T).zero_mem
  set l : List ((Xs → MvPolynomial (Fin m) K) × ℕ × G) :=
    ((Finset.univ : Finset (Fin m)).sigma sg).toList.map (fun p => (coefL p, 1, p.2)) with hl_def
  have hl : ∀ L ∈ l, L.1 ∈ S1 (K := K) T m ∧ 1 ≤ L.2.1 := by
    intro L hL
    rw [hl_def] at hL
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hL
    exact ⟨hcoef p, le_rfl⟩
  have hl1 : ∀ L ∈ l, L.2.1 = 1 := by
    intro L hL
    rw [hl_def] at hL
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hL
    rfl
  set Mt := (l.map (fun L => L.1 • rho r m L.2.2)).sum with hMt
  have hcore := core (rho r m) hS l hl (Fintype.card n)
  have hF : F (rho r m) l = Matrix.charpolyRev Mt := by
    unfold F Matrix.charpolyRev
    rw [F_eq _ l hl1]
  rw [hF] at hcore
  have hdet : Mt.det ∈ S1 (K := K) T m := by
    rw [det_eq_coeff]
    exact (S1 (K := K) T m).mul_mem ((S1 (K := K) T m).pow_mem
      ((S1 (K := K) T m).neg_mem (S1 (K := K) T m).one_mem) _) hcore
  have hx : ∀ x, Mt.det x = Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) K) •
      (a i x).map MvPolynomial.C) := by
    intro x
    rw [show Mt.det x = Pi.evalRingHom (fun _ : Xs => MvPolynomial (Fin m) K) x Mt.det from rfl,
      RingHom.map_det]
    congr 1
    rw [hMt, hl_def, map_list_sum, List.map_map, List.map_map, Finset.sum_map_toList,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hae i]
    refine Matrix.ext fun i' j' => ?_
    simp [coefL, rho, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Algebra.smul_def, map_mul]
  obtain ⟨t, ht, htx⟩ := hdet s
  exact ⟨t, ht, fun x => by rw [htx x]; exact congrArg (MvPolynomial.coeff s) (hx x)⟩

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
