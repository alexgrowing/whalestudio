import Mathlib

open scoped BigOperators
open Polynomial

namespace GlobalTheory.BlockDet

def blk {B : Type} {g n : ℕ} (M : Fin g → Fin g → Matrix (Fin n) (Fin n) B) :
    Matrix (Fin g × Fin n) (Fin g × Fin n) B :=
  Matrix.of fun pa qb => M pa.1 qb.1 pa.2 qb.2

def splitIdx (g n : ℕ) : Fin n ⊕ (Fin g × Fin n) ≃ Fin (g + 1) × Fin n where
  toFun := Sum.elim (fun a => (0, a)) (fun pa => (pa.1.succ, pa.2))
  invFun := fun pa => Fin.cases (motive := fun _ => Fin n ⊕ (Fin g × Fin n)) (Sum.inl pa.2)
    (fun p => Sum.inr (p, pa.2)) pa.1
  left_inv := by rintro (a | ⟨p, a⟩) <;> simp
  right_inv := by
    rintro ⟨p, a⟩
    refine Fin.cases ?_ (fun p => ?_) p <;> simp

theorem det_one_add_smul_blk_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B)
    (A : Subring (Matrix (Fin n) (Fin n) B)) (hdet : ∀ a ∈ A, a.det ∈ S) (e : B)
    (he : IsNilpotent e) (heA : ∀ a ∈ A, e • a ∈ A) (g : ℕ) :
    ∀ Θ : Fin g → Fin g → Matrix (Fin n) (Fin n) B, (∀ p q, Θ p q ∈ A) →
      (1 + e • blk Θ).det ∈ S := by
  induction g with
  | zero => intro Θ _; rw [Matrix.det_isEmpty]; exact S.one_mem
  | succ g ih =>
    intro Θ hΘ
    have hnil : IsNilpotent (⟨e • Θ 0 0, heA _ (hΘ 0 0)⟩ : A) := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k, Subtype.ext ?_⟩
      simp [_root_.smul_pow, hk]
    obtain ⟨w, hw⟩ := hnil.isUnit_one_add
    set u : Matrix (Fin n) (Fin n) B := ((w⁻¹ : Aˣ) : A).1 with hu
    have huA : u ∈ A := ((w⁻¹ : Aˣ) : A).2
    have hw' : ((w : A) : Matrix (Fin n) (Fin n) B) = 1 + e • Θ 0 0 := by rw [hw]; rfl
    letI : Invertible (1 + e • Θ 0 0) :=
      ⟨u, by rw [← hw', hu, ← Subring.coe_mul]; simp, by rw [← hw', hu, ← Subring.coe_mul]; simp⟩
    have hinv : ⅟(1 + e • Θ 0 0) = u := rfl
    let Bm : Matrix (Fin n) (Fin g × Fin n) B := Matrix.of fun a qb => Θ 0 qb.1.succ a qb.2
    let Cm : Matrix (Fin g × Fin n) (Fin n) B := Matrix.of fun pa b => Θ pa.1.succ 0 pa.2 b
    have h1 : (1 + e • blk Θ).submatrix (splitIdx g n) (splitIdx g n) =
        Matrix.fromBlocks (1 + e • Θ 0 0) (e • Bm) (e • Cm)
          (1 + e • blk (fun p q => Θ p.succ q.succ)) := by
      ext (a | ⟨p, a⟩) (b | ⟨q, b⟩) <;>
        simp [splitIdx, blk, Bm, Cm, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
    have h2 : (1 + e • blk (fun p q => Θ p.succ q.succ)) - (e • Cm) * u * (e • Bm) =
        1 + e • blk (fun p q => Θ p.succ q.succ - e • (Θ p.succ 0 * u * Θ 0 q.succ)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_sub_assoc, ← smul_sub]
      congr 2
    rw [← Matrix.det_submatrix_equiv_self (splitIdx g n), h1, Matrix.det_fromBlocks₁₁, hinv, h2]
    refine S.mul_mem (hdet _ (A.add_mem A.one_mem (heA _ (hΘ 0 0)))) (ih _ fun p q => ?_)
    exact A.sub_mem (hΘ _ _) (heA _ (A.mul_mem (A.mul_mem (hΘ _ _) huA) (hΘ _ _)))

def swapM {O X : Type} {n : ℕ} (a : X → Matrix (Fin n) (Fin n) O) :
    Matrix (Fin n) (Fin n) (X → O) :=
  Matrix.of fun i j x => a x i j

theorem det_sum_smul_mem {O X B : Type} [CommRing O] [CommRing B] (T : Subalgebra O (X → O))
    {n : ℕ} (ι : (X → O) →+* B) (S : Subring B) (hS : ∀ t ∈ T, ι t ∈ S) {m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O)
    (h : ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det
      (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T)
    (c : Fin m → B) (hc : ∀ k, c k ∈ S) :
    (∑ k, c k • (swapM (a k)).map ι).det ∈ S := by
  set D : MvPolynomial (Fin m) (X → O) := Matrix.det
    (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (swapM (a k)).map MvPolynomial.C)
    with hD
  have hco : ∀ d, MvPolynomial.coeff d D ∈ T := by
    intro d
    convert h d using 1
    funext x
    have : MvPolynomial.coeff d D x =
        MvPolynomial.coeff d (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) D) := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [this, hD, RingHom.map_det]
    congr 2
    ext i j : 1
    simp [swapM, Matrix.sum_apply]
  have hev : (∑ k, c k • (swapM (a k)).map ι).det = MvPolynomial.eval₂Hom ι c D := by
    rw [hD, RingHom.map_det]
    congr 1
    ext i j : 1
    simp [Matrix.sum_apply]
  rw [hev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hco d)) (S.prod_mem fun k _ => S.pow_mem (hc k) _)

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T) → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, Θ p q ∈ R) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro O X _ T n R hR g Θ hΘ
  set N := Fintype.card (Fin g × Fin n) with hN
  let I : Ideal (X → O)[X] := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : (X → O)[X] →+* (X → O)[X] ⧸ I := Ideal.Quotient.mk I
  let ι : (X → O) →+* (X → O)[X] ⧸ I := π.comp Polynomial.C
  let S : Subring ((X → O)[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.val.toRingHom)).range
  have hS : ∀ t ∈ T, ι t ∈ S := fun t ht => ⟨Polynomial.C ⟨t, ht⟩, by simp [ι]⟩
  have heS : π Polynomial.X ∈ S := ⟨Polynomial.X, by simp⟩
  have he : IsNilpotent (π Polynomial.X) :=
    ⟨N + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)⟩
  let G : Set (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    {M | ∃ a ∈ R, (swapM a).map ι = M}
  have hone : (1 : Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) ∈ G := by
    refine ⟨1, R.one_mem, ?_⟩
    have : swapM (1 : X → Matrix (Fin n) (Fin n) O) = 1 := by
      ext i j x
      simp [swapM, Matrix.one_apply, apply_ite (fun f : X → O => f x)]
    rw [this, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hmul : ∀ M ∈ G, ∀ M' ∈ G, M * M' ∈ G := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, R.mul_mem ha hb, ?_⟩
    rw [← Matrix.map_mul]
    congr 1
    ext i j x
    simp [swapM, Matrix.mul_apply]
  let A : Subalgebra S (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    (Submodule.span S G).toSubalgebra (Submodule.subset_span hone) (by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨M, hM, M', hM', rfl⟩
      exact hmul M hM M' hM')
  have hdet : ∀ a ∈ A.toSubring, a.det ∈ S := by
    intro a ha
    obtain ⟨m, c, f, rfl⟩ := Submodule.mem_span_set'.1 (show a ∈ Submodule.span S G from ha)
    choose b hb hbf using fun k => (f k).2
    have := det_sum_smul_mem T ι S hS b (hR m b hb) (fun k => c k) (fun k => (c k).2)
    simp only [hbf] at this
    exact this
  have key := det_one_add_smul_blk_mem S A.toSubring hdet (π Polynomial.X) he
    (fun a ha => A.smul_mem ha (⟨_, heS⟩ : S)) g (fun p q => (swapM (Θ p q)).map ι)
    (fun p q => Submodule.subset_span (R := S) (s := G) ⟨_, hΘ p q, rfl⟩)
  set M : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O) := blk fun p q => swapM (Θ p q) with hM
  set F : (X → O)[X] := Matrix.det ((Polynomial.X : (X → O)[X]) • M.map Polynomial.C +
    (1 : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O)).map Polynomial.C) with hF
  have hπ : (1 + π Polynomial.X • blk fun p q => (swapM (Θ p q)).map ι).det = π F := by
    rw [hF, RingHom.map_det, Matrix.map_one _ (map_zero _) (map_one _), map_add, map_one, add_comm]
    congr 2
  rw [hπ] at key
  obtain ⟨t, ht⟩ := key
  have hdvd : Polynomial.X ^ (N + 1) ∣ t.map T.val.toRingHom - F :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ht)
  have hc := Polynomial.X_pow_dvd_iff.1 hdvd N (Nat.lt_succ_self N)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, hF, hN, Polynomial.coeff_det_X_add_C_card,
    sub_eq_zero] at hc
  have hmem : M.det ∈ T := by rw [← hc]; exact (t.coeff _).2
  convert hmem using 1
  funext x
  exact ((Pi.evalRingHom (fun _ : X => O) x).map_det M).symm

end GlobalTheory.BlockDet
