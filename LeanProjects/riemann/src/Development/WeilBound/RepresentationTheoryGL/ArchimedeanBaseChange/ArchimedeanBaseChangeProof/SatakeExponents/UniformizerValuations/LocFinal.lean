import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsolateRepresentationAtCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfNonNilpotentVariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotientsStatement

namespace PositivityTheory.Rg.BcN.F2.Final

open PositivityTheory.Rg.BcN.F2

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ι : Type) [Fintype ι] [DecidableEq ι]

theorem hkAlg : HkAlg F ι := GlobalTheory.T.hecke_algebra_structure F ι
theorem prodFinLen : ProdFinLen F ι := GlobalTheory.T.finite_length_of_products F ι
theorem subOfNonNil' : SubOfNonNil' F ι := GlobalTheory.T.subquotient_of_non_nilpotent_variant F ι

end PositivityTheory.Rg.BcN.F2.Final
