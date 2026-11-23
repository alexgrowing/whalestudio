import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {m n : ℕ}

def IsUe (ε : Fin m → Bool) (X : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X = 0

def xyP (X : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (if b then star (X a c) else X a c) * MvPolynomial.X (c, i, b)

def vfX (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyP X a i false * pderiv (a, i, false) P + xyP X a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyP X a i false * MvPolynomial.X (a, i, true) + xyP X a i true * MvPolynomial.X (a, i, false)) * P)

def zRe (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - (sgn ε a * sgn ε b) • Matrix.single b a 1)

def zIm (ε : Fin m → Bool) (a b : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  (-(Complex.I / 2) : ℂ) • (Matrix.single a b 1 + (sgn ε a * sgn ε b) • Matrix.single b a 1)

open Classical in

def phiSF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (Ψ : Mx D m n → ℂ)
    (f : (Fin m → Fin n → ℂ) → ℂ) : schwartzA θ m n :=
  if h : tens θ τ fr f Ψ ∈ schwartzA θ m n then ⟨_, h⟩ else 0

def InvGroup : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ (t : ℝ) (P : PX V.rank n) (g : G D n),
      tens θ τ fr (fun y => fP (cLoc l τ) P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (Matrix.of y : Matrix (Fin V.rank) (Fin n) ℂ))) Ψ ∈ schwartzA θ V.rank n ∧
      thetaInt ω ν (phiSF θ τ fr Ψ (fun y => fP (cLoc l τ) P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (Matrix.of y : Matrix (Fin V.rank) (Fin n) ℂ)))) g =
        thetaInt ω ν (phiS θ τ fr (cLoc l τ) Ψ P) g

def DerivT : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ (P : PX V.rank n) (g : G D n),
      HasDerivAt (fun t : ℝ => thetaInt ω ν (phiSF θ τ fr Ψ (fun y => fP (cLoc l τ) P ((NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin V.rank) (Fin V.rank) ℂ) * (Matrix.of y : Matrix (Fin V.rank) (Fin n) ℂ)))) g)
        (thetaInt ω ν (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P)) g) 0

end PositivityTheory.Rg.Sw.Glob
