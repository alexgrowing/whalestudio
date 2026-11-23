import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GlobalTheory.EtC

namespace CrystallineSemistableComparison.E

theorem evExt : EvExt := fun R _ E I n α β =>
  ⟨(GlobalTheory.EtC.ev_basic R).2.2.1 α β, fun p s h U x =>
    let t := (GlobalTheory.EtC.ev_basic R).1 α β p s h U x; ⟨t.1, t.2.1, t.2.2.1⟩⟩

theorem evNat : EvNat := fun R _ E I n α p s h U =>
  ⟨fun V g x => ((GlobalTheory.EtC.ev_basic R).2.1 α p s h V U g x).symm, fun E' f x => (GlobalTheory.EtC.ev_basic R).2.2.2.1 f α p s h U x⟩

theorem evDel : EvDel := fun R _ E I n m hm β U =>
  ⟨(GlobalTheory.ev_delta_values R hm β U).1, fun p s t hs ht x => (GlobalTheory.ev_delta_values R hm β U).2 p s t hs _ x⟩

theorem inOp : InOp := fun S R _ _ I J ρ E n α β h => GlobalTheory.EtC.SemiMap.op_spec ρ E n α β h

end CrystallineSemistableComparison.E
