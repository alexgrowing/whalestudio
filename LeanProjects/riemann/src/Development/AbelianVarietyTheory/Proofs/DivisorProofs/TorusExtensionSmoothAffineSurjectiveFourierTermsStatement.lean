import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), Smooth Y.H.hom ∧ IsAffineHom Y.q.left ∧ Surjective Y.q.left ∧ IsMonHom Y.q ∧ ∀ (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ τ : SecK D.P.L Y.q.left k, IsTermOf Y b τ := by
  first | exact @GlobalTheory.Mum.ext_smooth_affine_surj_terms | exact GlobalTheory.Mum.ext_smooth_affine_surj_terms | (intros; apply GlobalTheory.Mum.ext_smooth_affine_surj_terms <;> assumption)
