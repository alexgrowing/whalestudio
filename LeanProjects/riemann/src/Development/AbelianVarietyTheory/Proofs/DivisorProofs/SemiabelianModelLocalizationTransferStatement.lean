import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelLocalizationTransfer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_model_localization_transfer : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (K : Type) [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] (a b : 𝓞 K), a ≠ 0 → b ≠ 0 → IsCoprime a b → (∃ (G : Over (Sp (Localization.Away (a : 𝓞 K)))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (a : 𝓞 K) →+* K), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K ∧ IsGrpPullback A G (spMap i) θ) → (∃ (G : Over (Sp (Localization.Away (b : 𝓞 K)))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (b : 𝓞 K) →+* K), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K ∧ IsGrpPullback A G (spMap i) θ) → HasModel A := by
  first | exact @GlobalTheory.BdFib.Glue.hasModel_of_coprime | exact GlobalTheory.BdFib.Glue.hasModel_of_coprime | (intros; apply GlobalTheory.BdFib.Glue.hasModel_of_coprime <;> assumption)
