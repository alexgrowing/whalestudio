import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
import Development.EtaleCohomology.EtaleSheaves.CxDescPf
import Development.EtaleCohomology.EtaleSheaves.DescentInduction.Bounds
import Development.EtaleCohomology.EtaleSheaves.LevelIdentPf
import Development.EtaleCohomology.EtaleSheaves.inclPf
import Development.EtaleCohomology.EtaleSheaves.longPf
import Development.EtaleCohomology.EtaleSheaves.longPfSes
import Development.EtaleCohomology.EtaleSheaves.shiftPf
import Development.EtaleCohomology.EtaleSheaves.stupidPf
import Development.EtaleCohomology.EtaleSheaves.CochainComplexSingleFunctorZeroMapFZero

namespace UpperTheory.Et.EtaleDescentEtaleAxioms

theorem a0 : LateralTheory.E.LevelIdentPf.FreeSingleHomotopyEquivDiscreteChains := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf
theorem a1 : LateralTheory.E.DescStepPf.LevelIdent := LateralTheory.E.LevelIdentPf.LevelIdent_of a0
theorem a2 : LateralTheory.E.stupidPf.trunc0 := LateralTheory.E.trunc0Pf.trunc0_of
theorem a3 : LateralTheory.E.stupidPf.incl := LateralTheory.E.inclPf.incl_of
theorem a4 : LateralTheory.E.CxDescPf.stupid := LateralTheory.E.stupidPf.stupid_of a2 a3
theorem a5 : LateralTheory.E.longPf.LES := GlobalTheory.T.hypercohomology_longExact_first_of_injective
theorem a6 : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPfSes.long_of a5
theorem a7 : LateralTheory.E.CxDescPf.shift := LateralTheory.E.shiftPf.shift_of
theorem a8 : LateralTheory.E.DescStepPf.CxDesc := LateralTheory.E.CxDescPf.CxDesc_of a4 a6 a7
theorem a9 : LateralTheory.E.t_E1Cut.DescStep := LateralTheory.E.DescStepPf.etale_descent_induction_of_levelwise_identity_and_complex_descent a1 a8

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.DescStep := a9

end UpperTheory.Et.EtaleDescentEtaleAxioms
