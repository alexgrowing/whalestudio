import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveV

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.CovTestDR GlobalTheory.EigWhole

namespace GlobalTheory.EigWholeDR

variable {D : D7} (O : Setup D)

def testG : Pol D.what₂.Tau O.N :=
  lamA D.what₂.Tau O.N O.j ^ (dimGr D.what₂.Tau O.N O.j - 1) * (fibPt D.what₂.Tau O.N O.j - vdmCl D.what₂.Tau O.N O.j)

def diffPolDR : MvPolynomial (Var O) ℝ :=
  (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2) * rename Sum.inl (testG O)

def RamModelDR : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    AwayAgree O ∅ R c →
    ∀ (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : Var O → GlobalTheory.HermLB M.p) (m : ℕ+)
      (Ψ : MvPolynomial (Var O) ℝ →ₗ[ℝ] ℝ),
      (∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (fam O ∅ R i)).Induced M (L i) m 0) →
      (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (O.var c).dim Ψ) →
      Ψ (diffPolDR O) = 0

end GlobalTheory.EigWholeDR

end
