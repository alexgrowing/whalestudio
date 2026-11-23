import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

abbrev MJ (j : ℕ) : Type := Matrix (Fin j) (Fin j) ℂ

def levi (k r j : ℕ) (x : MJ j) : Q.Mx k r := Matrix.of fun p q =>
  if hp : p.val < j then (if hq : q.val < j then x ⟨p.val, hp⟩ ⟨q.val, hq⟩ else 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      -conj (x ⟨2 * r + k - q.val, by omega⟩ ⟨2 * r + k - p.val, by omega⟩) else 0)
  else 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def EZ {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) h Z

def EZs {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ)) h Z

def ParamCommF {j : ℕ} (T : (MJ j → E) → (MJ j → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → MJ j → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => T (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

structure ZOp {j : ℕ} (T : (MJ j → E) → MJ j → E) : Prop where
  loc : ∀ (h₁ h₂ : MJ j → E) (Z : MJ j), h₁ =ᶠ[𝓝 Z] h₂ → T h₁ Z = T h₂ Z
  add : ∀ (V : Set (MJ j)) (h₁ h₂ : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h₁ V →
    ContDiffOn ℝ ∞ h₂ V → ∀ Z ∈ V, T (h₁ + h₂) Z = T h₁ Z + T h₂ Z
  smul : ∀ (V : Set (MJ j)) (c : ℂ) (h : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h V →
    ∀ Z ∈ V, T (c • h) Z = c • T h Z
  par : ParamCommF T

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

def CurveLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (x : MJ j) (t : ℝ),
    x0 k r j hj Z τ γ * NormedSpace.exp ((t : ℂ) • levi k r j x) =
      x0 k r j hj (Z * NormedSpace.exp ((t : ℂ) • x)) τ γ

def HpartLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j ≤ r) (a b : Fin j),
    hpart1 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) ∧
      hpart1 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ))

def XiCoef : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (a : Fin j)
    (p : Fin (2 * r + k + 1)),
    herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec p) (bvec (eI k r (Fin.castLE (by omega) a))) =
      if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def XiCoefV : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → ∀ (a : Fin j) (p : Fin (2 * r + k + 1)),
    ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE (by omega) a))) p =
      if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0

def XiMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Q.Glev k r 0

def XiSmooth : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ) {Z | Z.det ≠ 0}

def ZOpRd : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (x : MJ j), ZOp (E := E) (fun h => RdV x h)

def DzSlice : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (ℂ × (Fin j → Fin j → ℂ)))
    (κ : ℂ → MJ j → E), IsOpen U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U → ∀ τ₀ : ℂ,
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dz (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} ∧
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dzb (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U}

end Formalism.FourierDecayAlt.P.WirtingerOperators
