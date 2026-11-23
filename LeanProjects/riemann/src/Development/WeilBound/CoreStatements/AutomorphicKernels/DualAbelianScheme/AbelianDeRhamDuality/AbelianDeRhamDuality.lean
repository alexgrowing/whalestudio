import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianDeRhamPage
import Development.WeilBound.CoreStatements.AbelianDeRhamStructure.AbelianDeRhamPages.AbelianDeRhamStructureOfPage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual

set_option autoImplicit false

namespace PositivityTheory.DualRT

open GlobalTheory.Published

theorem surjAll : CrystallinePoints.Pd.SurjAll :=
  surjAll_of_hodge GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations MainStatements.Hodge.Free.abelianHodgeDeRham

theorem duality : AbelianDeRham.Duality :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  CrystallinePoints.Pd.duality_of_surjAll (GlobalTheory.abelianDeRhamStructure_toFree hS) hS.2.1 hS.2.2 surjAll

theorem abelianDeRham : AbelianDeRham :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham, duality⟩

end PositivityTheory.DualRT
