import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open IsLocalRing

theorem nonempty_torusExtension_of_comp_eq {K : Type} [Field K] {S S₁ S₂ : Scheme.{0}} {a : S₁ ⟶ S}
    {b : Spec (CommRingCat.of K) ⟶ S₁} {c : S₂ ⟶ S} {d : Spec (CommRingCat.of K) ⟶ S₂} (e : b ≫ a = d ≫ c)
    (G : Over S) [GrpObj G] (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback d).obj ((Over.pullback c).obj G))) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  have h₁ : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := ⟨torusExtOfIso (pullCompIso b a G).symm T⟩
  rw [e] at h₁
  obtain ⟨T₁⟩ := h₁
  exact ⟨torusExtOfIso (pullCompIso d c G) T₁⟩

theorem exists_finite_dvr_torusExtension_specialFibre : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [IsAdicComplete (IsLocalRing.maximalIdeal V') V'] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], IsSemiAbelian G → ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'') (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''), Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧ IsLocalHom (algebraMap V' V'') ∧ IsSemiAbelian (baseChange V' V'' G) ∧ Nonempty (TorusExtension (specialFibre V'' (baseChange V' V'' G))) := by
  intro V' _ _ _ _ G _ hG
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue V'))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  let k := ResidueField V'
  let Ω := AlgebraicClosure k
  obtain ⟨T⟩ := h₀.fibres Ω (spMap (algebraMap k Ω))
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range (algebraMap k Ω) _ T
  haveI : Finite s := hs.to_subtype
  haveI : FiniteDimensional k (IntermediateField.adjoin k s) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, e, he⟩ := nb V' (IntermediateField.adjoin k s)
  refine ⟨V'', i1, i2, i3, i4, i5, hf, hi, hl, IsSemiAbelian.pullback _ G hG, ?_⟩
  have hT := H _ (ResidueField.map (algebraMap V' V''))
    ((algebraMap (IntermediateField.adjoin k s) Ω).comp e.symm.toRingHom)
    (by
      rw [← he]
      ext x
      simp [k])
    (fun x hx => ⟨e ⟨x, IntermediateField.subset_adjoin _ _ hx⟩, by simp⟩)
  refine nonempty_torusExtension_of_comp_eq ?_ G hT
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ResidueField.map_comp_residue]
  rfl

end GlobalTheory
