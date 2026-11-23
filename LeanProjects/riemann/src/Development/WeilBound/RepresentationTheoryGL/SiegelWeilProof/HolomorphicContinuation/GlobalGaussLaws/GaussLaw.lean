import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def IsAwayFn {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (Ψ : Mx D m n → ℂ) : Prop :=
  ∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) → Ψ x = Ψ x'

def IsTrivAt (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop := compAt θ τ (mat x) = 1

def IsLocFact {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n)
    (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  (∀ y f, IsSch f → IsSch (L y f)) ∧ ∀ (y : GR n) Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
    (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L y f) Ψ

def epsT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) : Fin m → Bool := fun a => if 0 < t then ε a else !ε a

def gramB {m : ℕ} (ε : Fin m → Bool) (b : Bool) (y : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => evX (Qb ε b i j) y

def gZf {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true y).trace - Complex.I * c * (Zᴴ * gramB (epsT t ε) false y).trace)

def IsSiegel (Z : Matrix (Fin n) (Fin n) ℂ) : Prop := ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef

def actZ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂)⁻¹

def jF (e : ℤ) (p q : ℕ) (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (mR y).det ^ e * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂).det ^ (-(p : ℤ)) *
    ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂).det ^ (-(q : ℤ))

def GZSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSch (gZf ε t c Z)

def AwayAct : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ x : G D n, IsTrivAt θ τ x →
    ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
      ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

def DecompAway : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), IsTrivAt θ τ x ∧ g = x * ι y ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def LocFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocFact ω τ fr ι L

def GaussLaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) y Z *
        gZf ε (tLoc l τ) (cLoc l τ) (actZ y Z) u

def KPoly : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ k : GR n, InK (mR k) → ∀ P : PX V.rank n, ∃ P' : PX V.rank n, L k (fP (cLoc l τ) P) = fP (cLoc l τ) P'

end PositivityTheory.Rg.Sw.Glob
