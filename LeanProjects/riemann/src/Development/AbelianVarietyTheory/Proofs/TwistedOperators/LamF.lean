import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

def fmR {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    GlobalTheory.FockCompare.RW T S :=
  fun τ => fockMat A B τ (z τ)

def omF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) : ℝ :=
  GlobalTheory.OrientedHeis.omO S T (fmR A B z) (fmR A B e)

def gD {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) : ℝ :=
  2 * ∑ τ, ∑ i, ∑ j, c τ * (z τ i j * conj (e τ i j)).re

def lamF {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  (1 / 2 : ℂ) * (-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ)
    - (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ)
    - (1 / 2 : ℂ) * (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ)
    + (I / 2) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ))

def crOp {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (Φ : VCx D.what₂.Tau S.rank T.rank → ℂ) (z : VCx D.what₂.Tau S.rank T.rank) : ℂ :=
  lamF A B l z * Φ z + (1 / 2 : ℂ) *
    (fderiv ℝ Φ z (Formalism.L2.Ker.coordX l) - I * fderiv ℝ Φ z (I • Formalism.L2.Ker.coordX l))

end GlobalTheory.FockTransl.Jet

end
