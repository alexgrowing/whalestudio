import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOneStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem extend_isLocus_of_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  intro X _ _ hX V W hV hVW hW c hloc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨r, hr⟩ := IsLocus.exists_sec (pull_isLB hL W.ι) hloc
  obtain ⟨t, ht, -⟩ := ((GlobalTheory.extension_over_codim_two X hX).1 W hW).2.1 L r
  have e : GlobalTheory.secPull t W.ι = r := (GlobalTheory.lbSec_ext fun i => rfl).trans ht
  have h1 : W.ι ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t = W.ι ⁻¹ᵁ V := by
    rw [← GlobalTheory.nonzeroLocus_secPull, e, hr]
  have key : ∀ x (hx : x ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t ↔ x ∈ V := fun x hx => by
    have := congrArg (fun U : W.toScheme.Opens => (⟨x, hx⟩ : W.toScheme) ∈ U) h1
    exact Iff.of_eq this
  refine ⟨L, hL, t, rfl, ?_⟩
  exact GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' X hX V (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) hV (fun x hx => (key x (hVW hx)).2 hx)
    (fun z hz hz1 => (key z (hW z hz1)).1 hz)

end GlobalTheory
