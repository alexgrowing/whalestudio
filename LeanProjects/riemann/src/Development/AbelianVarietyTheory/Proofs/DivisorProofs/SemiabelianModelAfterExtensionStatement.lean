import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelAfterExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_model_after_extension : GlobalTheory.Published.SiegelToroidalIntegral → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp K)), ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K'), ∀ (K'' : Type) [Field K''] [NumberField K''] (j' : K' →+* K'') (A : Over (Sp K'')) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap (j'.comp j)) ψ → ∃ (G : Over (Sp (Localization.Away (n : 𝓞 K'')))) (_ : GrpObj G) (θ : A.left ⟶ G.left) (i : Localization.Away (n : 𝓞 K'') →+* K''), IsSemiAbelian G ∧ i.comp (algebraMap (𝓞 K'') _) = algebraMap (𝓞 K'') K'' ∧ IsGrpPullback A G (spMap i) θ := by
  first | exact @GlobalTheory.SiegelAway.exists_semiAbelian_model_away | exact GlobalTheory.SiegelAway.exists_semiAbelian_model_away | (intros; apply GlobalTheory.SiegelAway.exists_semiAbelian_model_away <;> assumption)
