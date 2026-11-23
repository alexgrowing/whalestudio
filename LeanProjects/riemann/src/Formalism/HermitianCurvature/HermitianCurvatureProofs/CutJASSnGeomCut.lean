import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GramSchmidtFramesLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfIso

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def nuG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)

def nuG' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g)

def PpG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Pm k r z' - PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) * PI.UnitaryGroupMassFormula.GsFr.Pm k r z'

def ioG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g

def posG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r z z' g}

def geG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r z z' g}

def GeomSmooth : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    B.CkOn ⊤ (posG k r z z') (nuG z z') ∧ B.CkOn ⊤ (posG k r z z') (nuG' z z') ∧
      B.CkOn ⊤ (posG k r z z') (ioG z z')

def GeomEqvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      nuG z z' g = h *ᵥ nuG z z' (h⁻¹ * n⁻¹ * g * n' * h') ∧
        nuG' z z' g = h' *ᵥ nuG' z z' (h⁻¹ * n⁻¹ * g * n' * h')

def GeomEqvIo : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      ioG z z' g = h * ioG z z' (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹

def GeomAtGq : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k →
    C2.StdZ k r z → C2.StdZ k r z' → IsSection k r z z' μsec →
    ∀ (c : Fin r → ℂ) (ζ : ℂ), (∀ l, c l ≠ 0) → Tz k r z * Tz k r z' < Complex.normSq ζ →
      nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ ∧
        nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ ∧
          ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ

def GeomBd0 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ C : ℝ, ∀ g ∈ posG k r z z', ‖nuG z z' g‖ ≤ C ∧ ‖nuG' z z' g‖ ≤ C ∧ ‖ioG z z' g‖ ≤ C

def UBLInvSqrt : Prop :=
  ∀ (k r d : ℕ) (P : B.Mat k r → ℂ), U.IsPolyDeg d P → ∀ (S : Set (B.Mat k r)), S ⊆ B.GV k r →
    ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (P g).re) → ∀ n : ℕ,
      UBL (fun g => (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ)) S n 0 d

def GeomUBL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' → ∀ ε : ℝ, 0 < ε →
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG' z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (ioG z z') (geG k r z z' ε) n e γ)

def GeomAssemble : Prop :=
  GeomSmooth → GeomEqvNu → GeomEqvIo → GeomAtGq → GeomBd0 → GeomUBL → SSnGeom

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
