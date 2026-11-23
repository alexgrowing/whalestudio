import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_of_isEE :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.HasTests → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hT hO hE
  have := hb.ft
  have := hb.char
  have h1 := classical_points_and_local_regularity o Ω M U₀ hO.normal
  have h2 := exists_at_test_of_cen o Ω S M U₀ hT hO
  have h3 := ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M U₀ hO
  have h4 := isoFree_TT_and_supI_specializes o Ω S M U₀ hO h1 h2 h3
  have h5 := EE_contains_stable_weightZero o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  have h6 := coord_regular_and_unit o Ω S M U₀ EE hO h1 h2 h3 h4 hE
  exact ⟨hO, hE, h1.2, fun z p _ y y₀ τ hc ha => (h3 z p y y₀ τ hc ha).2, h4.1, h4.2.2.1,
    fun ξ => (h5 ξ).1, fun ξ => (h5 ξ).2.1, fun ξ => (h5 ξ).2.2, h6⟩

end GlobalTheory.ZH
