import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_thetaPt_of_polarisedIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  first | exact @GlobalTheory.exists_level_thetaPt_of_polIso | exact GlobalTheory.exists_level_thetaPt_of_polIso | (intros; apply GlobalTheory.exists_level_thetaPt_of_polIso <;> assumption)
