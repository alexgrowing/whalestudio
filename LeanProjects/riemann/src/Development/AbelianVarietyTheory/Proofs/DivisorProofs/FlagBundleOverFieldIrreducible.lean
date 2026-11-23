import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsIrreducibleConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlagStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.FlagIrrFld

theorem isPreirreducible_of_connect {Y : Scheme.{0}}
    (h : ∀ y₁ y₂ : Y, ∃ (T : Scheme.{0}) (f : T ⟶ Y), IrreducibleSpace T ∧ y₁ ∈ Set.range f ∧ y₂ ∈ Set.range f) :
    IsPreirreducible (Set.univ : Set Y) := by
  rintro u v hu hv ⟨y₁, -, hy₁⟩ ⟨y₂, -, hy₂⟩
  obtain ⟨T, f, hT, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩⟩ := h y₁ y₂
  obtain ⟨t, -, ht⟩ := (IrreducibleSpace.isIrreducible_univ T).isPreirreducible _ _
    (hu.preimage f.continuous) (hv.preimage f.continuous) ⟨t₁, trivial, hy₁⟩ ⟨t₂, trivial, hy₂⟩
  exact ⟨f t, trivial, ht⟩

theorem nonempty_of_field (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type)
    [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : Nonempty Y := by
  have fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 (Spec (CommRingCat.of K)))).obj (E a)) (r a) :=
    fun a => (GlobalTheory.T.vector_bundle_over_field_has_flag K _ (r a) ((hE a).pullback _)).some
  obtain ⟨g', -, -⟩ := hF _ (𝟙 _) fl'
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨g' x⟩

theorem irreducibleSpace_of_isFlagBundle : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι]
    (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro K _ Y π ι _ E r fl hE hF
  haveI := nonempty_of_field K Y π ι E r fl hE hF
  refine { isPreirreducible_univ := isPreirreducible_of_connect fun y₁ y₂ => ?_, toNonempty := inferInstance }
  set p₁ := Y.fromSpecResidueField y₁
  set p₂ := Y.fromSpecResidueField y₂
  obtain ⟨x₁⟩ : Nonempty (Spec (Y.residueField y₁)) := inferInstance
  obtain ⟨x₂⟩ : Nonempty (Spec (Y.residueField y₂)) := inferInstance
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p₁ ≫ π) (g := p₂ ≫ π) x₁ x₂
    (Subsingleton.elim _ _)
  set P := pullback (p₁ ≫ π) (p₂ ≫ π)
  let L : Type := P.residueField z
  let u : Spec (CommRingCat.of L) ⟶ P := P.fromSpecResidueField z
  have hq : (u ≫ pullback.fst _ _ ≫ p₁) ≫ π = (u ≫ pullback.snd _ _ ≫ p₂) ≫ π := by
    simp only [Category.assoc]
    exact congrArg (u ≫ ·) pullback.condition
  obtain ⟨T, t₁, t₂, f, hT, h₁, h₂⟩ := GlobalTheory.T.flag_bundle_points_irreducible_connected _ Y π ι E r fl hE hF L _ _ hq
  obtain ⟨w⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  have m₁ : p₁ ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₁ := by
    have := Scheme.range_fromSpecResidueField y₁ ▸ Set.mem_range_self (f := p₁) ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  have m₂ : p₂ ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₂ := by
    have := Scheme.range_fromSpecResidueField y₂ ▸ Set.mem_range_self (f := p₂) ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  refine ⟨T, f, hT, ⟨t₁ w, ?_⟩, ⟨t₂ w, ?_⟩⟩
  · rw [← m₁, ← Scheme.Hom.comp_apply, h₁]; rfl
  · rw [← m₂, ← Scheme.Hom.comp_apply, h₂]; rfl

end GlobalTheory.FlagIrrFld
