import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneH

variable {D : D7} {n : ℕ}

def hhT (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) : GA D V :=
  atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹)

def CurveSt : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (ε : Fin V.rank → Bool) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → IsUe ε X →
    hhT θ V τ fr X 0 = 1 ∧ (∀ a b, hhT θ V τ fr X (a + b) = hhT θ V τ fr X a * hhT θ V τ fr X b) ∧
    ∀ Φ : schwartzA θ V.rank n,
      (∀ y : Mx D V.rank n, Continuous fun p : GA D V × ℝ =>
        Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X p.2)) (HMul.hMul (mt V p.1⁻¹) y))) ∧
      ∀ (z : Mx D V.rank n) (t : ℝ), HasDerivAt (fun u : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X u)) z))
        (DX θ V τ fr X Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X t)) z)) t

end PositivityTheory.Rg.Sw.Glob.DerOneH
