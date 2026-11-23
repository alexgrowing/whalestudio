import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

variable {D : D7}

def embAt (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) (k : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  cmp θ τ (stabilizerEmbedding d (atTau θ Y τ k))

def mco {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (v₀ : M.H τ) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : ℂ :=
  ⟪M.rep τ g₀ v₀, M.rep τ g (M.rep τ g₀ v₀)⟫_ℂ

def ptY {Y : HSp D} {S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S') (τ : D.what₂.Tau) (u : Formalism.REAL.UJ (M₀.ε τ)) :
    Matrix (Fin Y.rank) (Fin Y.rank) ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M₀ τ (Formalism.MainNotions.S.umat u)

structure LocOK (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar} (M₀ : DSModel Y S')
    (M : DSModel V S) (τ : D.what₂.Tau) (q : ℝ) (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ)
    (εB : Fin V.rank → Bool) (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ) (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : M₀.H τ) (c : ℂ) : Prop where

  unitA : IsUnit A

  gramA : Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ

  unitB : IsUnit B

  gramB : Bᴴ * Formalism.REAL.Jm εB * B = gramAt D V τ

  adapted : ∀ (y : Fin Y.rank → ℂ) (a : ℂ),
    eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2

  real : g₀ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)

  kfin : v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ

  dec : DecayAt M τ v₀ v₀ (2 * V.rank ^ 2 + 1)

  sm : w ∈ M₀.sm τ

  ne : w ≠ 0

  cne : c ≠ 0

  act : ∀ b : M₀.H τ, ∫ u, mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u)) * ⟪b, M₀.rep τ (ptY M₀ τ u) w⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    c * ⟪b, w⟫_ℂ

  far : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))) (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖mco M τ g₀ v₀ (g * embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖c‖

  lip : ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖mco M τ g₀ v₀ (embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * ptY M₀ τ u)) -
      mco M τ g₀ v₀ (embAt θ d τ (ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤ Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹)

end GlobalTheory.PackLoc

end
