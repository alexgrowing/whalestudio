import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteTwistingNotIsGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

noncomputable section
namespace GlobalTheory.VertTerm

abbrev Idx (D : D7) (N : ℕ) : Type := (Bool × Rt D.what₂.Tau N) ⊕ (Bool × (Fin (D.R.f * N) ⊕ Fin (D.R.f * N)))

def symOf {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) :
    Idx D N → Sym D.host.E →₀ ℤ :=
  Sum.elim (fun q => rootSym S.Dw (Function.update (ArIn.ind Sx) p q.1) (some R) (tauEmb D q.2.1) q.2.2)
    fun q => wholeSym (Function.update (ArIn.ind Sx) p q.1) (some R) q.2

def evIdx (D : D7) (N : ℕ) : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Idx D N) ℝ :=
  aeval fun v => match v with
    | Sum.inl q => X (Sum.inl q)
    | Sum.inr (b, k) => C ((k.factorial : ℝ)⁻¹) * ∑ l, X (Sum.inr (b, l)) ^ k

end GlobalTheory.VertTerm
end
