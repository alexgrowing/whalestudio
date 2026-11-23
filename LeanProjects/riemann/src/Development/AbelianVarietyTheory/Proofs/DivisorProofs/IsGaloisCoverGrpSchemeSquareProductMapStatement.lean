import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | exact GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | (intros; apply GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap <;> assumption)
