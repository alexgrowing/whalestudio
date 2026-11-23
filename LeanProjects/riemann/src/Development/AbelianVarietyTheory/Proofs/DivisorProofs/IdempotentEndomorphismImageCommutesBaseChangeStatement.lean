import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_endomorphism_image_commutes_base_change : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  first | (exact @GlobalTheory.ImgPB.image_idem_pullback) | (exact GlobalTheory.ImgPB.image_idem_pullback) | (intros; apply GlobalTheory.ImgPB.image_idem_pullback <;> assumption)
