import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

theorem projectiveBundleFormula_vectorBundle_any_space : D1 :=
  projectiveBundleFormula_of_unitOnEtalePoints fun q _ _ N V hq => GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces q N (GlobalTheory.T.projectiveBundleFormula_discrete_space q N) V hq

end GlobalTheory.EtC

end
