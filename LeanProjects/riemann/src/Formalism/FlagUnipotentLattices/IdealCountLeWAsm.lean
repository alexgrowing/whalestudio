import Formalism.FlagUnipotentLattices.IdealCountLeW
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted

namespace Formalism.HermitianLatticeCounting.Final.S6

theorem iotaDual : Formalism.HermitianLatticeCounting.S6.IotaDual := Formalism.HermitianLatticeCounting.P.embedding_dual_compatible
theorem iotaDetermined : Formalism.HermitianLatticeCounting.S6.IotaDetermined := Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction
theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index
theorem subGen : Formalism.HermitianLatticeCounting.S6.SubGen := Formalism.HermitianLatticeCounting.P.submodule_generator_count
theorem extGen : Formalism.HermitianLatticeCounting.S6.ExtGen := Formalism.HermitianLatticeCounting.P.extension_generator_count
theorem colonScale : Formalism.HermitianLatticeCounting.S6.ColonScale := Formalism.HermitianLatticeCounting.P.colon_ideal_scaling
theorem colonNorm : Formalism.HermitianLatticeCounting.S6.ColonNorm := Formalism.HermitianLatticeCounting.P.colon_ideal_norm
theorem idealCountEq : Formalism.HermitianLatticeCounting.S6.IdealCountEq := Formalism.HermitianLatticeCounting.P.ideal_count_eq
theorem idealCountLe : Formalism.HermitianLatticeCounting.S6.IdealCountLe := Formalism.HermitianLatticeCounting.P.quotient_card
theorem totientBound : Formalism.HermitianLatticeCounting.S6.TotientBound := Formalism.HermitianLatticeCounting.P.totient_bound_alt
theorem torsionBound : Formalism.HermitianLatticeCounting.S6.TorsionBound := Formalism.HermitianLatticeCounting.P.torsion_bound_alt
theorem cCount : Formalism.HermitianLatticeCounting.S6.CCount := Formalism.HermitianLatticeCounting.P.colon_count_bound
theorem cCount' : Formalism.HermitianLatticeCounting.S6.CCountAsm := Formalism.HermitianLatticeCounting.P.colon_count_of_hyp
theorem idealCountLeW : Formalism.HermitianLatticeCounting.S6.IdealCountLeW := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted
theorem idealCountLeWAsm : Formalism.HermitianLatticeCounting.S6.IdealCountLeW' := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp
theorem cCountW : Formalism.HermitianLatticeCounting.S6.CCountW := Formalism.HermitianLatticeCounting.P.colon_count_weighted
theorem cCountWAsm : Formalism.HermitianLatticeCounting.S6.CCountWAsm := Formalism.HermitianLatticeCounting.P.colon_count_weighted_of_hyp
theorem torsionBoundAsm : Formalism.HermitianLatticeCounting.S6.TorsionBoundAsm := Formalism.HermitianLatticeCounting.P.torsion_bound_of_totient
theorem quotCard : Formalism.HermitianLatticeCounting.S6.QuotCard := Formalism.HermitianLatticeCounting.P.height_loss_bound
theorem costBound : Formalism.HermitianLatticeCounting.S6.CostBound := Formalism.HermitianLatticeCounting.P.cost_bound
theorem hLoss : Formalism.HermitianLatticeCounting.S6.HLoss := Formalism.HermitianLatticeCounting.P.loss_bound_holds

end Formalism.HermitianLatticeCounting.Final.S6
