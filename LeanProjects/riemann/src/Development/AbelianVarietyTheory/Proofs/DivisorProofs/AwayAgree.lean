import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

variable {D : D7} (O : Setup D)

abbrev Var : Type := DV.Rt D.what₂.Tau O.N ⊕ (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))

def fam (T : Finset ℕ) (R : ℝ) : Var O → Sym D.host.E →₀ ℤ
  | .inl x => rootSym O.S.Dw (ArIn.ind T) (some R) (DV.tauEmb D x.1) x.2
  | .inr l => wholeSym (ArIn.ind T) (some R) l

def diffPol : MvPolynomial (Var O) ℝ :=
  (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2) *
    rename Sum.inl (curveCl D.what₂.Tau O.N O.j)

def AwayAgree (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) : Prop :=
  ∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt (O.var c)),
      ¬ resP v ∣ (NumberField.discr D.host.E).natAbs →
      lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inr k) 1) v ε y =
        lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inl (z.1, (z.2 : ℕ))) 1) v ε y

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

def RamModel : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    AwayAgree O (Pad.setB O.κ B) R c →
    ∀ (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : Var O → GlobalTheory.HermLB M.p) (m : ℕ+)
      (Ψ : MvPolynomial (Var O) ℝ →ₗ[ℝ] ℝ),
      (∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (fam O (Pad.setB O.κ B) R i)).Induced M (L i) m 0) →
      (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (O.var c).dim Ψ) →
      Ψ (diffPol O) = 0

end GlobalTheory.EigWhole

end
