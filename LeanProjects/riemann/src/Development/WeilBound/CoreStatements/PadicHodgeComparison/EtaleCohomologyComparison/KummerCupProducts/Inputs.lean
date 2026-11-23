import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeZeroOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EvExt

set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GlobalTheory.EtC

namespace CrystallineSemistableComparison.E

theorem inGen : InGen := fun q _ i =>
  let t := GlobalTheory.EtC.twist_sections q i; ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩

theorem inSch : InSch := GlobalTheory.EtC.sch_cls_cocycle_sec

theorem inTw : InTw := fun q _ i j => (GlobalTheory.EtC.TwPairUniq.main q i j).1

theorem inRed : InRed := GlobalTheory.EtC.RedExists.red_exists

theorem inKum : InKum := GlobalTheory.EtC.KummerSplit.isKum_kumT

theorem firstChern_cocycle_naturality : InC1 := fun q _ E L h => (GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity q).1 L h

theorem etale_a2_facts : A2 := GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology

theorem reduced_coefficient_facts : A11 := GlobalTheory.EtC.RedCoef.a11

theorem etIn : EtIn := ⟨etale_a2_facts, reduced_coefficient_facts, inGen, inSch, inTw, inRed, inOp, inKum, firstChern_cocycle_naturality⟩

end CrystallineSemistableComparison.E
