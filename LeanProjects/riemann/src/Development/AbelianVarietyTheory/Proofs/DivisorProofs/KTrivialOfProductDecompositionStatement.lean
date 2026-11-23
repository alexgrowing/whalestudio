import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTrivialOfProductDecomposition
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
theorem _root_.GlobalTheory.T.k_trivial_of_product_decomposition : ∀ {T : Scheme.{0}} {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂] (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂) [IsMonHom q₁] [IsMonHom q₂], IsLimit (BinaryFan.mk q₁ q₂) → ∀ {L₁ : LB B₁.left} (hL₁ : L₁.IsLB), Out.KTriv B₁ L₁ → ∀ {L₂ : LB B₂.left} (hL₂ : L₂.IsLB), Out.KTriv B₂ L₂ → ∀ {L : LB C.left} (hL : L.IsLB), cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂) → Out.KTriv C L := by
  first | exact @GlobalTheory.KTrivProduct.kTriv_prod | exact GlobalTheory.KTrivProduct.kTriv_prod | (intros; apply GlobalTheory.KTrivProduct.kTriv_prod <;> assumption)
