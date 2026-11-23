import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KSGraph

theorem connectedSpace_sp_dualNumber (k : Type) [Field k] : ConnectedSpace (Sp (DualNumber k)) := by
  change ConnectedSpace (PrimeSpectrum (DualNumber k))
  have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩

theorem exists_dim {k : Type} [Field k] (A' : Over (Sp (DualNumber k))) [GrpObj A']
    (hA' : IsAbelianScheme A') : ∃ g, SmoothOfRelativeDimension g A'.hom := by
  have := hA'.smooth
  have := hA'.geomConnected
  have := connectedSpace_sp_dualNumber k
  have : ConnectedSpace A'.left := GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap
  exact exists_dim_of_preconnected A'.hom (Classical.arbitrary _)

theorem isFilLift_iff_sub_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  intro k _ A₀ _ A' _ i h hA' x hx y y' hy
  obtain ⟨g, hg⟩ := exists_dim A' hA'
  have P := GlobalTheory.abelianDeRham
  have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 k A₀ g hA₀ g₀).1
  have reg := ksRegular_of_isAbelianScheme P h hA' hg
  constructor
  · intro hy'
    obtain ⟨w, hw, -⟩ := hL.1 y
    obtain ⟨w', hw', -⟩ := hL.1 y'
    have e := (reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩
    subst e
    exact hw'.sub_mem hw
  · intro hz
    obtain ⟨v, ⟨z, hz', -⟩, -⟩ := reg (y' - y) hz
    obtain ⟨d, hd, e⟩ := hy
    obtain ⟨d', hd', e'⟩ := hz'
    refine ⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]
    ext <;> simp

end GlobalTheory.KSGraph
