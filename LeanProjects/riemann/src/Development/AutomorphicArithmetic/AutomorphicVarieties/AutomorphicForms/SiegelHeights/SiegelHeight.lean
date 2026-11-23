import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace UpperTheory.V.Fb

def SmTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : GA E a → ℂ), φ ∈ TR.Sm E a → IsArchSmooth φ

def SmOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : GA E a → ℂ), IsArchSmooth φ → φ ∈ TR.Sm E a

def CptIff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (y : GL (Fin a) (TR.Rinf E)),
    grpEq E a y ∈ archCompact E a ↔ y.val ∈ Matrix.unitaryGroup (Fin a) (TR.Rinf E)

def KFinTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : TR.Sm E a),
    IsOpen {k | TR.finRep E a k φ = φ} →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => TR.cptRep E a k φ)) → IsKFinite φ.1

def HeightLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ), ∃ N : ℕ, ∀ y : GL (Fin a) (TR.Rinf E),
    AutomorphicForm.height (TR.infGL E a y) ≤ TR.height y ^ N

def HeightGe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (g : GA E a),
    TR.height (GeneralLinearGroup.map (TR.pInf E) g) ≤ 3 * AutomorphicForm.height g

def VecLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ (g : AdelicGLn.AdelicGL K n) (x : Fin n → K),
    x ≠ 0 → 1 ≤ C * AutomorphicForm.height g ^ N * Reduction.height g x

def DetBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ g : AdelicGLn.AdelicGL K n,
    (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ C * AutomorphicForm.height g ^ N

def SiegelHeight : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)), IsCompact ω →
    ω ⊆ (Reduction.adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) → ∀ t : ℝ, 0 < t →
    ∃ (C : ℝ) (N : ℕ), ∀ (g : AdelicGLn.AdelicGL K n) (γ : GL (Fin n) K),
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t →
      AutomorphicForm.height (AdelicGLn.diagonal K n γ * g) ≤ C * AutomorphicForm.height g ^ N

def SiegelFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)), IsCompact ω → ∀ t : ℝ,
    ∃ Ω : Set (AdelicGLn.FiniteAdelicGL K n), IsCompact Ω ∧ ∀ g ∈ Reduction.siegelSet n ω t, finPart g ∈ Ω

def GrowthTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (a : ℕ) (φ : TR.Sm E a),
    (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | TR.finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N) → HasModerateGrowth φ.1

def CuspTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (φ : GA E a → ℂ), IsLeftInvariant φ → Continuous φ →
    GlobalTheory.CuspRep.IsCuspidal φ → AutomorphicForm.IsCuspidal φ

def CuspOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (φ : GA E a → ℂ), IsLeftInvariant φ → Continuous φ →
    AutomorphicForm.IsCuspidal φ → GlobalTheory.CuspRep.IsCuspidal φ

end UpperTheory.V.Fb
