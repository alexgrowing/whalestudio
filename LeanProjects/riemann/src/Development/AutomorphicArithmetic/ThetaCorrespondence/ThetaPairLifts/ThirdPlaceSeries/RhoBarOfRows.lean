import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointStatementsOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
namespace PointStatements
section Loc
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
theorem built_anti_alt {big big' : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)} (h : ∀ w, big' w ⊆ big w)
    (hb : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L := by
  obtain ⟨Sp, hA, hs⟩ := hb
  exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
theorem eventuallyOfBuilt_mono_withLoc {P Q : D7 → Prop} (h : ∀ L : LocAll (lay0 D), P (withLoc L) → Q (withLoc L))
    (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q :=
  let ⟨b, hb⟩ := hP; ⟨b, fun L hL => h L (hb L hL)⟩
theorem eventuallyOfBuilt_and {P Q : D7 → Prop} (hP : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P) (hQ : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup Q) :
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P D' ∧ Q D' := by
  classical
  obtain ⟨b1, h1⟩ := hP
  obtain ⟨b2, h2⟩ := hQ
  exact ⟨fun w => b1 w ∪ b2 w, fun L hL => ⟨h1 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_left) hL),
    h2 L (_root_.GlobalTheory.HeightCounting.Up.PointStatements.built_anti_alt (fun w => Finset.subset_union_right) hL)⟩⟩
end Loc
theorem residualIrreducibleGood_of_inputs (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (I : _root_.GlobalTheory.NRows.LinkedInputs hL D) (R : _root_.GlobalTheory.NRows.PointConditions' D) : AutomorphicSideWildInertia.ResidualIrreducibleGood D :=
  _root_.Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime_alt D
    ⟨R.a.tieLab, _root_.GlobalTheory.AdmTame.main_alt_alt_alt D R.a.tie0 R.a.a2 R.a.a5 (_root_.GlobalTheory.TieLabAt.main_alt_alt hL D I.P).2.1⟩
    R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
end PointStatements
end GlobalTheory.HeightCounting.Up
end
end
