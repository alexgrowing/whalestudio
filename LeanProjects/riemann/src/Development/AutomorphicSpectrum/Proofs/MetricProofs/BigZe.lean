import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

def tz {I : Type} [Fintype I] (Z : Matrix I I ℂ) (z : I → ℂ) : I → ℂ := z - Z *ᵥ star z

abbrev Ix (Ψ : Type) (j j' : ℕ) : Type := (Fin j' ⊕ Fin j) × Ψ

def emb {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (i : Ix Ψ j j') : 𝓞 E →+* ℂ :=
  Sum.elim (fun _ => σ i.2) (fun _ => (starRingEnd ℂ).comp (σ i.2)) i.1

def bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ :=
  blockDiagonal fun τ => fromBlocks 0 (ballMat q t τ)ᵀ (ballMat q t τ) 0

def bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (t : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (bigZ q t).submatrix e.symm e.symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
