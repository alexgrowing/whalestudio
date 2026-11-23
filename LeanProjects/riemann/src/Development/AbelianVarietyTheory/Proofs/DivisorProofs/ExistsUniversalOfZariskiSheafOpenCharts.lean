import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafOfOpenImmersionLocalGlueStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_universal_of_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) := by
  intro F hsep hglue Ix U x inj hW cov
  have hF : Presieve.IsSheaf Scheme.zariskiTopology F := GlobalTheory.T.isSheaf_of_open_immersion_local_glue F hsep hglue
  let W : ∀ (_ : Ix) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens :=
    fun i Z y => Classical.choose (hW i Z y)
  have hWs : ∀ i (Z : Scheme.{0}) (y : F.obj (op Z)) (Y : Scheme.{0}) (a : Y ⟶ Z),
      (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W i Z y :=
    fun i Z y => Classical.choose_spec (hW i Z y)
  have hrep : F.IsRepresentable := by
    refine GeneratorFunctor.isRepresentable_of_charts F hF U x W ?_ ?_ ?_
    · intro j Z y Z' a
      rw [Set.range_subset_iff]
      refine ((hWs j Z y Z' a).symm.trans ?_)
      exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
    · intro j Z g g' h
      exact inj j Z g g' h
    · intro Z y z
      obtain ⟨i, Y, a, u, ⟨q, rfl⟩, h⟩ := cov Z y z
      exact ⟨i, (hWs i Z y Y a).1 ⟨u, h⟩ q⟩
  refine ⟨F.reprX, F.reprx, fun T y => ?_⟩
  refine ⟨F.representableBy.homEquiv.symm y, ?_, ?_⟩
  · have := F.representableBy.homEquiv_eq (F.representableBy.homEquiv.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro g hg
    apply F.representableBy.homEquiv.injective
    rw [Equiv.apply_symm_apply, F.representableBy.homEquiv_eq, ← hg]
    rfl

end GlobalTheory
