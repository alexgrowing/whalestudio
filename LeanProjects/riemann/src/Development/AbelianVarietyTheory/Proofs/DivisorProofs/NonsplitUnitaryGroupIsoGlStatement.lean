import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnitaryGroupIsoGl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.EulerTw
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonsplit_unitary_group_iso_gl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E), ¬ IsSplitAt u → ∃ e : GlobalTheory.EulerTw.Gam E n u ≃ₜ* GLw n u, ∀ g, e g = GeneralLinearGroup.map (pLoc E u) g.1 := by
  first | exact @GlobalTheory.EulerTw.GamInert.main | exact GlobalTheory.EulerTw.GamInert.main | (intros; apply GlobalTheory.EulerTw.GamInert.main <;> assumption)
