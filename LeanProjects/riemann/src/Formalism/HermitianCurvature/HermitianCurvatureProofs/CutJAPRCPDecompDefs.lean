import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
