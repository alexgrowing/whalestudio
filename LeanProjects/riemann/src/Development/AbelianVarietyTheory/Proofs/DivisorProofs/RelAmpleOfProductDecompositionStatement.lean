import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfProductDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitModelToPlaceModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam pull)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)
open MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_ample_of_product_decomposition : ∀ {T : Scheme.{0}} [IsAffine T] {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂], IsAbelianScheme B₁ → IsAbelianScheme B₂ → ∀ (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂), IsLimit (BinaryFan.mk q₁ q₂) → ∀ {L₁ : LB B₁.left} (hL₁ : L₁.IsLB), Out.RelAmple B₁ L₁ → ∀ {L₂ : LB B₂.left} (hL₂ : L₂.IsLB), Out.RelAmple B₂ L₂ → ∀ {L : LB C.left} (hL : L.IsLB), cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂) → Out.RelAmple C L := by
  first | exact @GlobalTheory.ProdAmple.relAmple_of_cls_eq_add | exact GlobalTheory.ProdAmple.relAmple_of_cls_eq_add | (intros; apply GlobalTheory.ProdAmple.relAmple_of_cls_eq_add <;> assumption)
