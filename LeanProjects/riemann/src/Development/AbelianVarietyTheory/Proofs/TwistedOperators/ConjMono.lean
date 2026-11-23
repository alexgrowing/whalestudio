import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

section Pure

variable {ι : Type} [Fintype ι] {a b : ℕ}

def gq (c : ι → ℝ) (z : VCx ι a b) : ℝ := ∑ τ, ∑ i, ∑ j, c τ * ‖z τ i j‖ ^ 2

def bk (c : ι → ℝ) (z₀ z : VCx ι a b) : ℂ := ∑ τ, ∑ i, ∑ j, (c τ : ℂ) * z₀ τ i j * conj (z τ i j)

def conjMono (m : DVar ι a b →₀ ℕ) (z : VCx ι a b) : ℂ := m.prod fun k n => conj (z k.1 k.2.1 k.2.2) ^ n

end Pure

variable {D : D7}

def fw (D : D7) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * ‖tauE D τ D.host.xi0‖

def fockMat {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  ∑ i, ∑ j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
    ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j))

def fockPt (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T)
    (z : VCx D.what₂.Tau S.rank T.rank) : WO S T :=
  GlobalTheory.FockCompare.iotaW σ T S fun τ => fockMat A B τ (z τ)

def rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ) (x : WO S T) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x

theorem fw_pos (D : D7) (τ : D.what₂.Tau) : 0 < fw D τ := by
  unfold fw
  have h : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  positivity

end GlobalTheory.FockTransl

end
