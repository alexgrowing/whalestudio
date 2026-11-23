import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FactsAtMembership
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.NFacts.AtMemFacts
theorem oneField_of_nAt_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : Formalism.L2.Host.CharFrame D} {C : NChoice D} {tp : Formalism.L2.Host.TupTied D cf C}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) : GlobalTheory.HeightCounting.SameTw.OneField D C := by
  have key : ∀ X : Σ (D₁ : D7) (c₁ : Formalism.L2.Host.CharFrame D₁) (C₁ : NChoice D₁), Formalism.L2.Host.TupTied D₁ c₁ C₁,
      X = ⟨withLoc a.nt.L, cfL a.nt.L a.nt.cf, chL a.nt.L a.nt.C, tpL a.nt.L a.nt.tp⟩ →
        GlobalTheory.HeightCounting.SameTw.OneField X.1 X.2.2.1 := by
    rintro _ rfl
    exact (GlobalTheory.HeightCounting.SameTw.oneField_withLoc a.nt.L a.nt.C).2 a.nt.Sp.tw_reads
  exact key _ a.nt.pack
end GlobalTheory.NFacts.AtMemFacts
end
end
