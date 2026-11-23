import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

def coOf {a : ℕ} (T : Matrix (Fin a) (Fin a) ℂ) : HCo a := (fun i => (T i i).re, fun p => T p.1.1 p.1.2)

def uU {m : ℕ} (u : {p : Fin m × Fin m // p.1 < p.2} → ℂ) : Matrix (Fin m) (Fin m) ℂ := fun i j =>
  if h : i < j then u ⟨(i, j), h⟩ else if i = j then 1 else 0

def frameT (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Tup k r (r + 1) := fun i b => fvec k r z b i

def IsFibC (k r a : ℕ) (fib : HCo a → Measure (Tup k r a)) : Prop :=
  IsFibreFamily ((2 : ℝ≥0∞) ^ ((2 * r + k + 1) * a) • (volume : Measure (Tup k r a))) gramC hOf
    {X | LinearIndependent ℂ fun b i => X i b} ((2 : ℝ≥0∞) ^ (a * (a - 1) / 2) • (volume : Measure (HCo a)))
    Set.univ fib

def muSn {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p : Mt k r × Mt k r => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j

def nCoords (k r : ℕ) (x : Mt k r) :
    ({p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) // p.1.val < r ∧ p.1 < p.2 ∧ p.2.val ≤ r + k} → ℂ) ×
      ({p : Fin r × Fin r // p.1 < p.2} → ℂ) × (Fin r → ℝ) :=
  (fun p => x p.1.1 p.1.2, fun p => x (eI k r p.1.1) (esI k r p.1.2), fun a => (x (eI k r a) (esI k r a)).im)

section Ring

variable {A : Type} [CommRing A]

def sideM {n a b : ℕ} (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin n) (Fin b) A) :
    Matrix (Fin n) (Fin (a + b)) A := fun i => Fin.append (P i) (Q i)

def blockM {a b : ℕ} (P : Matrix (Fin a) (Fin a) A) (Q : Matrix (Fin a) (Fin b) A)
    (R : Matrix (Fin b) (Fin a) A) (S : Matrix (Fin b) (Fin b) A) : Matrix (Fin (a + b)) (Fin (a + b)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P Q R S)

def T1 (r : ℕ) (T : A) : Matrix (Fin (r + 1 + r)) (Fin (r + 1 + r)) A :=
  blockM (TF r T) (Matrix.of fun a b => if a = Fin.castSucc b then 1 else 0)
    (Matrix.of fun b a => if a = Fin.castSucc b then 1 else 0) 0

def T2 (σ : A →+* A) (r : ℕ) (T T' : A) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    Matrix (Fin (r + 1 + (r + 1))) (Fin (r + 1 + (r + 1))) A := blockM (TF r T) Z (cT σ Z) (TF r T')

def T3 (σ : A →+* A) (r : ℕ) (T T' c : A) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) A) :
    Matrix (Fin (r + 1 + (r + 1))) (Fin (r + 1 + (r + 1))) A :=
  cT σ (blockM 1 (-(c • 1)) 0 (c • 1)) * T2 σ r T T' Z * blockM 1 (-(c • 1)) 0 (c • 1)

end Ring

section Glob

variable {E : Type} [Field E] [NumberField E]

def id1 (E : Type) [Field E] [NumberField E] (r : ℕ) : Fin (r + 1 + r) → FractionalIdeal (𝓞 E)⁰ E :=
  Fin.append (fun b : Fin (r + 1) => dInv E (r - (b : ℕ))) fun b : Fin r => (dInv E (r - (b : ℕ)))⁻¹

def id2 (E : Type) [Field E] [NumberField E] (r : ℕ) : Fin (r + 1 + (r + 1)) → FractionalIdeal (𝓞 E)⁰ E :=
  Fin.append (fun b : Fin (r + 1) => dInv E (r - (b : ℕ))) fun b : Fin (r + 1) => dInv E (r - (b : ℕ))

def Adapted {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (s : Fin r → ℝ) : Prop :=
  ∀ (w : InfinitePlace E) (a : Fin r),
    (A w).mulVec (fun i => w.embedding (P i a.castSucc)) = (s a : ℂ) • bvec (eI k r a) ∧
    (A w).mulVec (fun i => w.embedding (f i a)) = ((s a)⁻¹ : ℂ) • bvec (esI k r a)

def IsDomN (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (𝓓 : Set (InfinitePlace E → Mt k r)) : Prop :=
  MeasurableSet 𝓓 ∧ ∀ x : InfinitePlace E → Mt k r, (∀ w, Matrix.of (x w) ∈ Nset k r) →
    ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E, (InN σ J P γ ∧ latMap γ Λ = Λ) ∧
      (fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))) ∈ 𝓓

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

open scoped Classical in

def aV (E : Type) [Field E] [NumberField E] [Algebra F E] (k r : ℕ) (T : 𝓞 F)
    (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  GlobalTheory.SgDen.densF (Ideal.absNorm v.asIdeal) (eta₃ E v) (2 * r + k + 1) (r + 1 + r)
    (if T ∈ v.asIdeal then 1 else 0)

end Glob

end GlobalTheory.SnMass
