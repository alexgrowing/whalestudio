import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalDualModel

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

namespace ChernSpan

variable {R : Type} [CommRing R]

def blockSum {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin (M + N)) (Fin (M + N)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 b)

def kron {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    Matrix (Fin (M * N)) (Fin (M * N)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) a b)

abbrev Pair (M : ℕ) : Type := {p : Fin M × Fin M // p.1 < p.2}

abbrev pairCard (M : ℕ) : ℕ := Fintype.card (Pair M)

def pairEquiv (M : ℕ) : Fin (pairCard M) ≃ Pair M := (Fintype.equivFin (Pair M)).symm

def wedgeRaw {M : ℕ} (a : Matrix (Fin M) (Fin M) R) : Matrix (Pair M) (Pair M) R :=
  Matrix.of fun p q => a p.1.1 q.1.1 * a p.1.2 q.1.2 - a p.1.2 q.1.1 * a p.1.1 q.1.2

def wedge2 {M : ℕ} (a : Matrix (Fin M) (Fin M) R) : Matrix (Fin (pairCard M)) (Fin (pairCard M)) R :=
  Matrix.reindex (pairEquiv M).symm (pairEquiv M).symm (wedgeRaw a)

def wedgeLieRaw {M : ℕ} (L : Matrix (Fin M) (Fin M) R) : Matrix (Pair M) (Pair M) R :=
  Matrix.of fun p q =>
    L p.1.1 q.1.1 * (1 : Matrix (Fin M) (Fin M) R) p.1.2 q.1.2 +
      (1 : Matrix (Fin M) (Fin M) R) p.1.1 q.1.1 * L p.1.2 q.1.2 -
      L p.1.2 q.1.1 * (1 : Matrix (Fin M) (Fin M) R) p.1.1 q.1.2 -
      (1 : Matrix (Fin M) (Fin M) R) p.1.2 q.1.1 * L p.1.1 q.1.2

def wedge2Lie {M : ℕ} (L : Matrix (Fin M) (Fin M) R) : Matrix (Fin (pairCard M)) (Fin (pairCard M)) R :=
  Matrix.reindex (pairEquiv M).symm (pairEquiv M).symm (wedgeLieRaw L)

section Laws

variable {M N : ℕ}

theorem blockSum_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).map f = blockSum (a.map f) (b.map f) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem blockSum_one : blockSum (1 : Matrix (Fin M) (Fin M) R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [blockSum, Matrix.fromBlocks_one]

theorem blockSum_mul (a a' : Matrix (Fin M) (Fin M) R) (b b' : Matrix (Fin N) (Fin N) R) :
    blockSum (a * a') (b * b') = blockSum a b * blockSum a' b' := by
  simp [blockSum, Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv]

theorem blockSum_transpose (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    blockSum aᵀ bᵀ = (blockSum a b)ᵀ := by
  simp [blockSum, Matrix.fromBlocks_transpose, Matrix.transpose_submatrix]

theorem kron_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (kron a b).map f = kron (a.map f) (b.map f) := by
  ext i j
  simp [kron]

theorem kron_one : kron (1 : Matrix (Fin M) (Fin M) R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [kron, Matrix.one_kronecker_one]

theorem kron_mul (a a' : Matrix (Fin M) (Fin M) R) (b b' : Matrix (Fin N) (Fin N) R) :
    kron (a * a') (b * b') = kron a b * kron a' b' := by
  simp [kron, Matrix.mul_kronecker_mul, Matrix.submatrix_mul_equiv]

theorem kron_transpose (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R) :
    kron aᵀ bᵀ = (kron a b)ᵀ := by
  ext i j
  simp [kron]

theorem sum_sum_eq_sum_pair (F : Fin M → Fin M → R) :
    ∑ x, ∑ y, F x y = ∑ r : Pair M, (F r.1.1 r.1.2 + F r.1.2 r.1.1) + ∑ x, F x x := by
  have key : ∀ G : Fin M → Fin M → R, ∑ r : Pair M, G r.1.1 r.1.2 = ∑ x, ∑ y, if x < y then G x y else 0 := by
    intro G
    rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin M × Fin M => p.1 < p.2) (fun x => by simp)
      (fun p => G p.1 p.2), Finset.sum_filter, Fintype.sum_prod_type]
  have key' := key (fun x y => F y x)
  rw [Finset.sum_add_distrib, key, key']
  have h : ∀ x y, F x y = (if x < y then F x y else 0) + (if y < x then F x y else 0) + (if x = y then F x y else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.2 h.le]
  calc ∑ x, ∑ y, F x y
      = ∑ x, ∑ y, ((if x < y then F x y else 0) + (if y < x then F x y else 0) + (if x = y then F x y else 0)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h x y
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · congr 1
          rw [Finset.sum_comm]
        · refine Finset.sum_congr rfl fun x _ => ?_
          simp [eq_comm]

theorem wedge2_map {S : Type} [CommRing S] (f : R →+* S) (a : Matrix (Fin M) (Fin M) R) :
    (wedge2 a).map f = wedge2 (a.map f) := by
  ext p q
  simp [wedge2, wedgeRaw]

theorem wedgeRaw_one : wedgeRaw (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  simp only [wedgeRaw, Matrix.of_apply, Matrix.one_apply, Subtype.mk.injEq, Prod.mk.injEq]
  have h0 : (if j = k then (1 : R) else 0) * (if i = l then 1 else 0) = 0 := by
    by_cases h3 : j = k
    · by_cases h4 : i = l
      · subst h3; subst h4; exact absurd (hij.trans hkl) (lt_irrefl _)
      · simp [h4]
    · simp [h3]
  rw [h0, sub_zero]
  by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2]

theorem wedgeRaw_mul (a b : Matrix (Fin M) (Fin M) R) : wedgeRaw (a * b) = wedgeRaw a * wedgeRaw b := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  rw [Matrix.mul_apply]
  show (a * b) i k * (a * b) j l - (a * b) j k * (a * b) i l = ∑ r : Pair M,
    (a i r.1.1 * a j r.1.2 - a j r.1.1 * a i r.1.2) * (b r.1.1 k * b r.1.2 l - b r.1.2 k * b r.1.1 l)
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have e : ∀ x y, a i x * b x k * (a j y * b y l) - a j x * b x k * (a i y * b y l)
      = (a i x * a j y - a j x * a i y) * (b x k * b y l) := fun x y => by ring
  simp only [e]
  rw [sum_sum_eq_sum_pair]
  have hz : ∑ x, (a i x * a j x - a j x * a i x) * (b x k * b x l) = 0 :=
    Finset.sum_eq_zero fun x _ => by ring
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem wedgeRaw_transpose (a : Matrix (Fin M) (Fin M) R) : wedgeRaw aᵀ = (wedgeRaw a)ᵀ := by
  ext p q
  simp only [wedgeRaw, Matrix.of_apply, Matrix.transpose_apply]
  ring

theorem wedge2_one : wedge2 (1 : Matrix (Fin M) (Fin M) R) = 1 := by
  simp [wedge2, wedgeRaw_one]

theorem wedge2_mul (a b : Matrix (Fin M) (Fin M) R) : wedge2 (a * b) = wedge2 a * wedge2 b := by
  simp [wedge2, wedgeRaw_mul, Matrix.submatrix_mul_equiv]

theorem wedge2_transpose (a : Matrix (Fin M) (Fin M) R) : wedge2 aᵀ = (wedge2 a)ᵀ := by
  simp [wedge2, wedgeRaw_transpose, Matrix.transpose_submatrix]

end Laws

end ChernSpan

namespace PolyRep

variable {ι : Type} {m : ι → ℕ}

open ChernSpan

theorem evEnt_blockSum {M N : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    (Q : Matrix (Fin N) (Fin N) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (blockSum P Q) A = blockSum (evEnt P A) (evEnt Q A) := by
  have h := blockSum_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P Q
  simpa [evEnt] using h

theorem evEnt_kron {M N : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    (Q : Matrix (Fin N) (Fin N) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (kron P Q) A = kron (evEnt P A) (evEnt Q A) := by
  have h := kron_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P Q
  simpa [evEnt] using h

theorem evEnt_wedge2 {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ))
    {R : Type} [CommRing R] (A : Mat m R) :
    evEnt (ChernSpan.wedge2 P) A = ChernSpan.wedge2 (evEnt P A) := by
  have h := wedge2_map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2).toRingHom P
  simpa [evEnt] using h

def zero (m : ι → ℕ) : PolyRep m where
  M := 0
  ent := 0
  one R _ := by ext i; exact i.elim0
  mul R _ A B := by ext i; exact i.elim0
  transp R _ A := by ext i; exact i.elim0

def triv (m : ι → ℕ) : PolyRep m where
  M := 1
  ent := 1
  one R _ := by ext i j; simp [evEnt, Matrix.one_apply]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.one_apply]
  transp R _ A := by ext i j; simp [evEnt, Matrix.one_apply, eq_comm]

def sum (ρ σ : PolyRep m) : PolyRep m where
  M := ρ.M + σ.M
  ent := blockSum ρ.ent σ.ent
  one R _ := by rw [evEnt_blockSum, ρ.one R, σ.one R, blockSum_one]
  mul R _ A B := by rw [evEnt_blockSum, evEnt_blockSum, evEnt_blockSum, ρ.mul R, σ.mul R, blockSum_mul]
  transp R _ A := by rw [evEnt_blockSum, evEnt_blockSum, ρ.transp R, σ.transp R, blockSum_transpose]

def nsum (ρ : PolyRep m) (k : ℕ) : PolyRep m :=
  Nat.rec (zero m) (fun _ σ => σ.sum ρ) k

def tensor (ρ σ : PolyRep m) : PolyRep m where
  M := ρ.M * σ.M
  ent := kron ρ.ent σ.ent
  one R _ := by rw [evEnt_kron, ρ.one R, σ.one R, kron_one]
  mul R _ A B := by rw [evEnt_kron, evEnt_kron, evEnt_kron, ρ.mul R, σ.mul R, kron_mul]
  transp R _ A := by rw [evEnt_kron, evEnt_kron, ρ.transp R, σ.transp R, kron_transpose]

def wedge2 (ρ : PolyRep m) : PolyRep m where
  M := pairCard ρ.M
  ent := ChernSpan.wedge2 ρ.ent
  one R _ := by rw [evEnt_wedge2, ρ.one R, wedge2_one]
  mul R _ A B := by rw [evEnt_wedge2, evEnt_wedge2, evEnt_wedge2, ρ.mul R, wedge2_mul]
  transp R _ A := by rw [evEnt_wedge2, evEnt_wedge2, ρ.transp R, wedge2_transpose]

def ptr [Fintype ι] (ρ : PolyRep m) (i : ℕ) {S : Type} [CommRing S] (A : Mat m S) : S :=
  ((ρ.lie A) ^ i).trace

end PolyRep

namespace ChernSpan

variable {ι : Type}

def Reach [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] : Submodule ℝ (Mat m S → S) :=
  Submodule.span ℝ (Set.range fun ρ : PolyRep m => fun A : Mat m S => (Matrix.charpolyRev (-(ρ.lie A))).coeff n)

def trProd {m : ι → ℕ} (l : List (ι × ℕ)) {S : Type} [CommRing S] (A : Mat m S) : S :=
  (l.map fun x => ((A x.1) ^ x.2).trace).prod

def TrSpan (m : ι → ℕ) (w : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] : Submodule ℝ (Mat m S → S) :=
  Submodule.span ℝ {f | ∃ l : List (ι × ℕ), (∀ x ∈ l, 1 ≤ x.2) ∧ (l.map Prod.snd).sum = w ∧ f = fun A => trProd l A}

end ChernSpan

end GlobalTheory.GoodMetric
