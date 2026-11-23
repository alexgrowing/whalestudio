import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPartOfPulledActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiPolarizationFiniteExtensionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

namespace GlobalTheory.TorusPart

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  refine ⟨?_⟩
  rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

theorem exists_polarised_extension_finite : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G']
    (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ → PolPart c i' →
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), FiniteDimensional K K' ∧
      ∃ (G₂ : Over (Sp K')) (_ : GrpObj G₂) (i₂ : OAct O G₂) (φ₂ : G₂.left ⟶ G.left)
        (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u₂ : splitTorus (Sp K') X ⟶ G₂)
        (P : Out.PolAV (Sp K')) (q₂ : G₂ ⟶ P.A) (j₂ : OAct O P.A),
        IsActPull i₂ i (spMap (algebraMap K K')) φ₂ ∧ IsMonHom u₂ ∧ IsKer u₂ q₂ ∧ (∀ a, i₂.act a ≫ q₂ = q₂ ≫ j₂.act a) ∧
        IsRosati c P j₂ := by
  intro O _ _ c K Ω _ _ _ _ G _ hG i G' _ i' φ hφ ⟨T, P, e, j, he, hj, hR⟩
  letI := T.addCommGroup
  letI := T.grpB
  haveI := T.free
  haveI := T.finite
  obtain ⟨F, hF, G₀, _, i₀, φ₀, Y, _, _, _, u₀, B, _, q₀, j₀, ψ, h₀, hB, hu₀, hK₀, hq₀, hψ⟩ :=
    GlobalTheory.T.torus_part_of_pulled_action O K Ω G hG i G' i' φ hφ T.X T.i P.A (T.q ≫ e.hom) j P.isAb T.i_hom
      ((isKer_torusExtension T).comp_iso e he) hj
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := K) F
  obtain ⟨F', hF', P₁, j₁, ψ₁, hψ₁, hR₁⟩ := GlobalTheory.T.rosati_polarization_finite_extension O c F Ω B hB j₀ P j ψ hψ hR
  haveI := hG.comm
  haveI := isCommMonObj_of_isGrpPullback h₀.1
  obtain ⟨G₂, _, i₂, φ₂, h₂⟩ : ∃ (G₂ : Over (Sp F')) (_ : GrpObj G₂) (i₂ : OAct O G₂) (φ₂ : G₂.left ⟶ G₀.left),
      IsActPull i₂ i₀ (spMap (algebraMap F F')) φ₂ := ⟨_, _, _, _, exists_isActPull (spMap (algebraMap F F')) i₀⟩
  obtain ⟨u₂, hu₂, -⟩ := existsUnique_torusCompat h₂.1.1 u₀
  obtain ⟨q₂, hK₂, sq⟩ := IsKer.baseChange h₂.1 hψ₁.1 hu₂ hK₀
  refine ⟨F', inferInstance, inferInstance, Module.Finite.trans F F', G₂, inferInstance, i₂, φ₂ ≫ φ₀, Y, inferInstance,
    inferInstance, inferInstance, u₂, P₁, q₂, j₁, ?_, hu₂.isMonHom h₂.1, hK₂, fun a => ?_, hR₁⟩
  · have h := h₂.comp h₀
    have hs : spMap (algebraMap F F') ≫ spMap (algebraMap K F) = spMap (algebraMap K F') := by
      rw [← Spec.map_comp]; rfl
    rwa [hs] at h
  · refine Over.OverMorphism.ext (hψ₁.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ₁.2, ← sq.w, ← Category.assoc, h₂.2,
      Category.assoc, ← Over.comp_left, hq₀, Over.comp_left, ← Category.assoc, sq.w, Category.assoc]

end GlobalTheory.TorusPart
