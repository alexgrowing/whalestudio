import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem hodgeFiltration_lift_map_eq_crystalline_kernel (H : CrystallineSmoothLift) {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0)
    {π : R →+* R₀} (hπ : Function.Surjective π) (hk : RingHom.ker π = I) {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
    {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : IsPullback i s₀ s (spMap π)) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) (S : Sys I π s₀) (hP : S.Presents s i)
    (m : IsMor (dp0 R) s (divided₂ hI) (s₀ ≫ spMap π) (RingHom.id R) i) :
    (F1 s).map m.pull1 = S.K hI := by
  have hb := (H.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk X X₀ s s₀ i hs hs' hs'' h m).1
  obtain ⟨e, he, -⟩ := GlobalTheory.T.hodge_cohomology_iso_presented_crystal R R₀ I hI π hπ hk X₀ s₀ S X s i h hP
  have key : ∀ c, m.pull1 c ∈ S.K hI ↔ c ∈ F1 s := fun c ↦ by
    change S.r hI (m.pull1 c) = 0 ↔ toH1O s c = 0
    rw [← he m c, LinearEquiv.map_eq_zero_iff, structureSheaf_comparison_comm]
    exact ⟨fun h0 ↦ cmpO_injective R X s (h0.trans (map_zero _).symm), fun h0 ↦ by rw [h0, map_zero]⟩
  ext x
  obtain ⟨c, rfl⟩ := hb.2 x
  constructor
  · rintro ⟨c', hc', e'⟩
    rw [← hb.1 e']
    exact (key c').2 hc'
  · intro hx
    exact ⟨c, (key c).1 hx, rfl⟩

theorem hodgeFiltration_lift_eq_comap_systemFiltration (H : CrystallineSmoothLift) (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀))
    [GrpObj A₀] (hA : IsProper A₀.hom) (hA' : GeometricallyConnected A₀.hom) (X : Over (Sp R))
    (i : A₀.left ⟶ X.left) (h : IsPullback i A₀.hom X.hom (spMap π)) (hX : Smooth X.hom) (S : Sys I π A₀.hom)
    (hP : S.Presents X.hom i) :
    primitiveCrystalHodgeLiftClasses (divided₂ hI) A₀ X i h.w = (S.K hI).comap (prim (divided₂ hI) (spMap π) A₀).subtype := by
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk, hI]⟩
  have hpr := (GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift R R₀ π hπ hnil X A₀ i h hX hA hA').1
  have e : X.hom ≫ 𝟙 _ = X.hom := Category.comp_id _
  have h' : IsPullback i A₀.hom (X.hom ≫ 𝟙 _) (spMap π) := by rw [e]; exact h
  have hs : Smooth (X.hom ≫ 𝟙 _) := by rw [e]; exact hX
  have hs' : IsSeparated (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hs'' : QuasiCompact (X.hom ≫ 𝟙 _) := by rw [e]; infer_instance
  have hP' : S.Presents (X.hom ≫ 𝟙 _) i := by rw [e]; exact hP
  unfold primitiveCrystalHodgeLiftClasses
  rw [hodgeFiltration_lift_map_eq_crystalline_kernel H hI hπ hk h' hs hs' hs'' S hP']

end GlobalTheory.LiftSys
