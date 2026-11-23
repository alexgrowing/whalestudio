import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionLiftNilpotentOfSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift

theorem exists_section_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  refine GlobalTheory.T.smooth_section_lift_nilpotent_of_sqZero ?_
  intro R R₀ _ _ π hπ hsq X X₀ i hpb hsm e₀ he₀
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hsq]; rfl⟩
  let g₀ := e₀ ≫ i
  have hg₀ : g₀ ≫ X.hom = spMap π := by
    simp only [g₀, Category.assoc]; rw [hpb.w, ← Category.assoc, he₀, Category.id_comp]
  let J : Set R := {h | ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ h V}
  have hS2 := GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine R R₀ π hπ hnil X hsm g₀ hg₀
  have hspan : Ideal.span J = ⊤ := by
    by_contra hne
    obtain ⟨N, hN, hJN⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfJ⟩ := hS2 ⟨N, hN.isPrime⟩
    exact hf (hJN (Ideal.subset_span hfJ))
  obtain ⟨s, hsJ, hs⟩ := (Ideal.span_eq_top_iff_finite J).1 hspan
  have hV : ∀ k : s, ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ k.1 V := fun k => hsJ k.2
  choose V hVa hVl using hV
  obtain ⟨e, he1, he2⟩ :=
    GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero R R₀ π hπ hsq X hsm g₀ hg₀ s (fun k => k.1) (by simpa using hs) V hVa hVl
  exact ⟨e, he1, he2.symm⟩

end GlobalTheory.SecLift
