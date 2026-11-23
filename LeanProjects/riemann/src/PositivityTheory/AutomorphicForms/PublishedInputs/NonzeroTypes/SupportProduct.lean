import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpUniq
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpRes
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector

namespace UpperTheory.TNZ.Grp

theorem step_suppProd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SupportOfProductProp :=
  step_spTop G UpperTheory.TNZ.step_spLat (step_spUniq G) (step_spCount G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) step_spOrd (step_spPiSub G) (step_spSupp G) UpperTheory.TNZ.step_cuspSupp UpperTheory.TNZ.step_prodIrr
    UpperTheory.TNZ.step_tensorVec

end UpperTheory.TNZ.Grp
