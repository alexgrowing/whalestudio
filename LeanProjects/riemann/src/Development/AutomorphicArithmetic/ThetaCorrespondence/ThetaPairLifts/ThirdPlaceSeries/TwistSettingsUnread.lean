import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicSideTransfer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeightCounting
theorem twist_settings_unread_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (N : TwNew D), (∃ A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE, A'.row = N.row A.row ∧ (∀ lam, A'.pl.ι lam = A.pl.ι lam) ∧ (∀ w a, A'.wdT.e w a = A.wdT.e w a) ∧ (∀ j h1 h2 π, A'.au.cls j h1 h2 π = A.au.cls j h1 h2 π) ∧ ∀ hL, (Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT) → Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL N.toD7 A'.wdT)) ∧ (_root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au → _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL N.toD7 A'.wdT A'.au)) ∧ (∀ M tup Q, MtInput D M tup Q → MtInput N.toD7 (N.mt M) tup Q) ∧ (BlocksUnique D → BlocksUnique N.toD7) := by
  intro D cf jE A N
  let A' : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding N.toD7 (N.cf cf) jE :=
    { bare := A.bare
      wdT := A.wdT
      lab := A.lab
      chr := { A.chr with }
      row := N.row A.row
      pl := { A.pl with }
      iota := A.iota
      wd := { A.wd with }
      grp := { A.grp with }
      par := { A.par with }
      au := { A.au with }
      chiT := A.chiT }
  refine ⟨⟨A', rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun hL => ⟨fun ⟨h⟩ => ⟨{ h with }⟩, fun h => h⟩⟩,
    fun M tup Q h => { h with }, fun h => h⟩
end GlobalTheory.HeightCounting
end
