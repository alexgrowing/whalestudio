import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSheafLocalModelBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSectionsFormFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFrameTransitionCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualFrameCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmEx
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenImmersionGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingOfMinimal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.VB GlobalTheory.ChainPts

namespace GlobalTheory.TanSec

theorem bijective_xAll {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) : Function.Bijective (xAll S) := by
  have hg : Function.Bijective (letters S.Dw).get :=
    ⟨List.nodup_iff_injective_get.1 (GlobalTheory.Proof.LetterConjugation.nodup_letters _),
      fun x => List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters _ x)⟩
  exact hg.comp (finCongr (length_letters S).symm).bijective

example {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (h : Nonempty (Letter S.Dw)) : 0 < D.R.f * N :=
  Fin.pos_iff_nonempty.2 ((bijective_xAll S).2 h.some).nonempty

end GlobalTheory.TanSec
