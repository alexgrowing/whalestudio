import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_baseChange_polarisedAbelian : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  first | exact @GlobalTheory.exists_level_baseChange | exact GlobalTheory.exists_level_baseChange | (intros; apply GlobalTheory.exists_level_baseChange <;> assumption)
