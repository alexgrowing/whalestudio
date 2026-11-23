import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real
open Formalism.REAL (GlRel)

variable {n : ℕ}

def nsq (x : Fin n → ℝ) : ℝ := ∑ a, x a ^ 2

def inCone (lev : Fin n → ℕ) (Q : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → lev a < lev b) ∧
    ∀ x, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))

structure Model (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Type 1 where
  W : Type
  [nacg : NormedAddCommGroup W]
  [ips : InnerProductSpace ℂ W]
  F1 : Fin n → Fin n → Module.End ℂ W
  F2 : Fin n → Fin n → Module.End ℂ W
  f : W
  gl1 : GlRel F1
  gl2 : GlRel F2
  comm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b
  unitK : ∀ a b (x y : W), ⟪kF F1 F2 a b x, y⟫_ℂ = ⟪x, kF F1 F2 b a y⟫_ℂ
  locFin : ∀ x : W, ∃ S : Submodule ℂ W, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S
  ch1 : ∀ m (x : W), gelA F1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x
  ch2 : ∀ m (x : W), gelA (barF F2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x
  hw : f ∈ hwSp F1 F2 (muQ lam lev)
  ne : f ≠ 0
  cone : ∀ (ν : Fin n → ℝ) (x : W), x ∈ hwSp F1 F2 ν → x ≠ 0 → inCone lev (ν - muQ lam lev)

attribute [instance] Model.nacg Model.ips

def N1 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev lev' : Fin n → ℕ, IsLev lam lev → IsLev lam lev' →
    inCone lev (muQ lam lev' - muQ lam lev) → muQ lam lev' = muQ lam lev

def ConeWeightsNotSecondType : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν : Fin n → ℝ,
    inCone lev (ν - muQ lam lev) → ¬ IsSecondTypeWeight lam lev ν

def ModelEx : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → Nonempty (Model lam lev)

def AdmLeast : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ lev : Fin n → ℕ, IsLev lam lev → hwSp E1 E2 (muQ lam lev) ≠ ⊥ →
      (∀ lev' : Fin n → ℕ, IsLev lam lev' → hwSp E1 E2 (muQ lam lev') ≠ ⊥ →
        nsq (muQ lam lev + rhoV n) ≤ nsq (muQ lam lev' + rhoV n)) → AdmFor lam lev E1 E2

def KTypeGenerationHighest : Prop :=
  MultFor → ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → AdmFor lam lev E1 E2 → ∀ (M : Model lam lev), (∀ ν, IsSecondTypeWeight lam lev ν → hwSp M.F1 M.F2 ν = ⊥) →
      ∀ v : V, v ∈ hwSp E1 E2 (muQ lam lev) → v ≠ 0 → ∀ (ν : Fin n → ℝ) (x : V), x ∈ hwSp E1 E2 ν → x ≠ 0 →
        (∃ a ∈ alg E1 E2, a v = x) → inCone lev (ν - muQ lam lev)

end PositivityTheory.RgBcC.RealD
