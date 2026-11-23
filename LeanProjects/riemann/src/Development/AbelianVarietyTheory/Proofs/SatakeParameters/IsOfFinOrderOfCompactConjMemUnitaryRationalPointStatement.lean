import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)), IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  first | exact @GlobalTheory.isOfFinOrder_of_conj_mem_ratU | exact GlobalTheory.isOfFinOrder_of_conj_mem_ratU | (intros; apply GlobalTheory.isOfFinOrder_of_conj_mem_ratU; all_goals assumption)
