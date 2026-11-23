import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def tupIn {M n : ℕ} (L : Set (R ⊗[F] E)) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∀ i k, X i k ∈ L}

def eMat {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)).updateCol l a

def dMat {n : ℕ} (l : Fin n) (s : R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Matrix.diagonal (Function.update 1 l s)

def cjM (σ : E →ₐ[F] E) {n : ℕ} (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ * y * g

def nearNF {M n : ℕ} (O L : Set (R ⊗[F] E)) (t : R ⊗[F] E) (j : ℕ) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | X ∈ tupIn R L ∧ ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
    ∀ k, ∑ i, X i k * a i ∈ (fun x => t ^ j * x) '' L}

def goodT {M n : ℕ} (O L : Set (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  tupIn R L \ ⋃ p ∈ S, nearNF R O L (p.1 : R ⊗[F] E) j

def gramIn (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ y ∈ Y, gramR R σ J X = (y : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def cjPre (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Y : Set (HermR R σ n)) :
    Set (HermR R σ n) :=
  {y | ∃ z ∈ Y, cjM R σ g (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (z : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

variable [TopologicalSpace R] [MeasurableSpace R]

def IsOrdData (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (O : Subring (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) : Prop :=
  IsCompact (O : Set (R ⊗[F] E)) ∧ IsOpen (O : Set (R ⊗[F] E)) ∧ (∀ x ∈ O, sigR R σ x ∈ O) ∧
  (∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O ∧ p.2 ≠ 0 ∧ (∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) ∧
    Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : R ⊗[F] E) ^ j) Filter.atTop (nhds 0) ∧
    ∃ θ : ℝ≥0, θ < 1 ∧ ∀ Y : Set (R ⊗[F] E),
      coordK R b lam ((fun x => (p.1 : R ⊗[F] E) * x) '' Y) = θ * coordK R b lam Y) ∧
  ∀ (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E), ¬ LinearIndependent (R ⊗[F] E) X →
    ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, p.2 * ∑ i, X i k * a i = 0

end Alg

section Help

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_mul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_assoc _ _ _

theorem hR_sum_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E)
    (y : Fin n → Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J x (fun k => ∑ e, y e k * w e) = ∑ e, hR R σ J x (y e) * w e := by
  simp only [hR, hform, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_sum_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin n → Fin M → R ⊗[F] E)
    (y : Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J (fun k => ∑ c, x c k * w c) y = ∑ c, sigR R σ (w c) * hR R σ J (x c) y := by
  simp only [hR, hform, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cjM R σ g (gramR R σ J X) := by
  ext a c
  change hR R σ J (fun i => ∑ e, X e i * g e a) (fun i => ∑ e, X e i * g e c) = _
  rw [hR_sum_right]
  simp only [hR_sum_left]
  rfl

theorem cjM_mul (σ : E →ₐ[F] E) {n : ℕ} (g h y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ (g * h) y = cjM R σ h (cjM R σ g y) := by
  simp only [cjM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cjM_one (σ : E →ₐ[F] E) {n : ℕ} (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ 1 y = y := by
  simp [cjM, Matrix.map_one, map_zero, map_one]

theorem cjM_mem (σ : E →ₐ[F] E) (hσ : ∀ x, sigR R σ (sigR R σ x) = x) {n : ℕ}
    (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hy : y ∈ HermR R σ n) : cjM R σ g y ∈ HermR R σ n := by
  intro a c
  have hy' : ∀ a c, sigR R σ (y c a) = y a c := hy
  simp only [cjM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, hσ, hy']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Fin n → R ⊗[F] E :=
  fun i => if i = l then 1 else - a i

theorem eMat_mul_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    eMat R l a * eMat R l (negCol R l a) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, eMat, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hk : k = l
  · subst hk
    simp only [if_true, negCol]
    have : ∀ c, (if c = k then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else - a c) =
        (if c = k then a i else 0) + (if c = i then (if i = k then 0 else - a i) else 0) := by
      intro c
      by_cases h1 : c = k
      · subst h1
        by_cases h2 : c = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : c = i
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : i = k
    · subst h; simp [hl]
    · simp [h]
  · simp only [hk, if_false]
    have : ∀ c, (if c = l then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else 0) =
        if c = k then (if i = k then 1 else 0) else 0 := by
      intro c
      by_cases h1 : c = k
      · subst h1; simp [hk]
      · simp [h1]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem dMat_mul {n : ℕ} (l : Fin n) (s t : R ⊗[F] E) (h : s * t = 1) : dMat R l s * dMat R l t = 1 := by
  rw [dMat, dMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = l
  · subst hi; simpa using h
  · simp [Function.update_of_ne hi]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem isCompact_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsCompact L) :
    IsCompact (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hL

end Help

end GlobalTheory.CompanionTheory.AvgFree
