import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.MainNotions.S

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def opn {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))‖

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

def CkOnH {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (H : Matrix (Fin n) (Fin n) ℂ) (m : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUH H g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ m F U ∧ ∀ g ∈ U, inUH H g → f g = F g

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def IsCC2 (k r : ℕ) (A : ℝ) (mm : ℕ) (F : Mx k r → V) : Prop :=
  CkOnH (Hpk k r) mm F ∧
    ∀ wl wr : List (Mx k r), wl.length + wr.length ≤ mm → (∀ X ∈ wl, InLieHpk k r X) →
      (∀ X ∈ wr, InLieHpk k r X) → ∃ C : ℝ, ∀ g ∈ UH (Hpk k r),
        ‖ldWord wl (rdWord wr F) g‖ ≤ C * opn g ^ (-A)

def genLie (k r : ℕ) (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) : Mx k r :=
  if p.2.2 then hpart2 (Hpk k r) (Matrix.single p.1 p.2.1 1) else hpart1 (Hpk k r) (Matrix.single p.1 p.2.1 1)

def ccNorm (k r : ℕ) (A : ℝ) (p : ℕ) (F : Mx k r → V) : ENNReal :=
  ⨆ (wl : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))
    (wr : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (_ : wl.length + wr.length ≤ p)
    (g : Mx k r) (_ : g ∈ UH (Hpk k r)),
      ENNReal.ofReal (opn g ^ A * ‖ldWord (wl.map (genLie k r)) (rdWord (wr.map (genLie k r)) F) g‖)

def IsCCs (k r : ℕ) (A : ℝ) (F : Mx k r → V) : Prop :=
  SmoothOnH (Hpk k r) F ∧
    ∀ wl wr : List (Mx k r), (∀ X ∈ wl, InLieHpk k r X) → (∀ X ∈ wr, InLieHpk k r X) →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk k r),
        ‖ldWord wl (rdWord wr F) g‖ ≤ C * opn g ^ (-A + 3 * ((r : ℝ) + 1) * ((wl.length + wr.length : ℕ) : ℝ))

def IsKKs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A : ℝ) (F : Mx k r → V) : Prop :=
  IsCCs k r A F ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ UH (Hpk k r), F g ≠ 0 → ε ≤ Gf k r z z' g

abbrev Env (n : ℕ) := List (Fin n × Fin n) →₀ ℂ

def envMul {n : ℕ} (X Y : Env n) : Env n :=
  X.sum fun w c => Y.sum fun w' c' => Finsupp.single (w ++ w') (c * c')

def EnvDegLe {n : ℕ} (X : Env n) (p : ℕ) : Prop := ∀ w ∈ X.support, w.length ≤ p

def envOfMat {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : Env n :=
  ∑ a, ∑ b, Finsupp.single [(a, b)] (Y a b)

def eWord (k r : ℕ) (w : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (F : Mx k r → V) : Mx k r → V :=
  w.foldr (fun p G => EabH (Hpk k r) p.1 p.2 G) F

def rOp (k r : ℕ) (X : Env (2 * r + k + 1)) (F : Mx k r → V) : Mx k r → V :=
  fun g => X.sum fun w c => c • eWord k r w F g

def thOp (k r : ℕ) {ι : Type} [Fintype ι] (a : ι → Mx k r → ℂ) (X : ι → Env (2 * r + k + 1))
    (F : Mx k r → V) : Mx k r → V :=
  fun g => ∑ i, a i g • rOp k r (X i) F g

def thAt (k r : ℕ) {ι : Type} [Fintype ι] (a : ι → Mx k r → ℂ) (X : ι → Env (2 * r + k + 1))
    (γ : Mx k r) : Env (2 * r + k + 1) :=
  ∑ i, a i γ • X i

def IsInvOp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (O : Set (Mx k r)) (p : ℕ)
    (Θ : (Mx k r → V) → Mx k r → V) : Prop :=
  ∀ F : Mx k r → V, CkOnH (Hpk k r) p F → ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', ∀ g ∈ O,
    Θ (fun x => F (s⁻¹ * x * s')) g = Θ F (s⁻¹ * g * s')

end GlobalTheory.SOrb
