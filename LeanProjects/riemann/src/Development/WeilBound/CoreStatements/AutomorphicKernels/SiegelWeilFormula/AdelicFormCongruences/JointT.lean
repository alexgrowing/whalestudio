import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ProjectedBlockUpperSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.CongUnip

namespace PositivityTheory.SiegelWeilFormula.Afc

theorem afc_all : OrbRes ∧ UEx ∧ (AuxiliaryPrimeFunction → FcConj) := ⟨orbRes, uEx, fcConj_of⟩

end PositivityTheory.SiegelWeilFormula.Afc
