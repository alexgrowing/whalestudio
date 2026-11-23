import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published.SemiAbelianHomExtension.Edge

open GlobalTheory.ExtUnique

def Concl {S : Scheme.{0}} (U : S.Opens) (G H : Over S) [GrpObj G] [GrpObj H] : Prop :=
  ∀ f : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj H, IsMonHom f →
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback U.ι).map F = f

theorem iff_concl : SemiAbelianHomExtension ↔
    ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
      ∀ (U : S.Opens), Dense (U : Set S) → ∀ (G H : Over S) [GrpObj G] [GrpObj H],
        IsSemiAbelian G → IsSemiAbelian H → Concl U G H := Iff.rfl

theorem concl_of_exists {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U : S.Opens) (hU : Dense (U : Set S)) (G H : Over S)
    [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (h : ∀ f : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj H, IsMonHom f →
      ∃ F : G ⟶ H, (Over.pullback U.ι).map F = f) : Concl U G H := by
  have := GlobalTheory.IsNormalScheme.of_pred hS
  obtain ⟨_, _⟩ := dense_open U hU
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  intro f hf
  obtain ⟨F, rfl⟩ := h f hf
  exact ⟨F, ⟨isMonHom_of_pullback U.ι F hf, rfl⟩, fun F' hF' => pullback_map_injective U.ι G H hF'.2⟩

theorem concl_top {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (G H : Over S)
    [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) : Concl ⊤ G H := by
  refine concl_of_exists hS ⊤ (by simp) G H hG hH fun f _ => ?_
  have : IsIso (⊤ : S.Opens).ι := inferInstanceAs (IsIso S.topIso.hom)
  refine ⟨Over.homMk (inv (pullback.fst G.hom (⊤ : S.Opens).ι) ≫ f.left ≫ pullback.fst H.hom (⊤ : S.Opens).ι) ?_,
    ?_⟩
  · rw [Category.assoc, Category.assoc, IsIso.inv_comp_eq, pullback.condition, pullback.condition,
      ← Category.assoc]
    exact congrArg (· ≫ (⊤ : S.Opens).ι) (Over.w f)
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (pullback_map_left_fst _ _).trans ?_
      exact IsIso.hom_inv_id_assoc _ _
    · exact (Over.w _).trans (Over.w _).symm

theorem concl_unit_left {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U : S.Opens) (hU : Dense (U : Set S)) (H : Over S)
    [GrpObj H] (hG : IsSemiAbelian (𝟙_ (Over S))) (hH : IsSemiAbelian H) : Concl U (𝟙_ (Over S)) H := by
  refine concl_of_exists hS U hU _ H hG hH fun f hf => ⟨η, ?_⟩
  have h := hf.one_hom
  rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, toUnit_unique η (𝟙 _),
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h.symm

theorem concl_unit_right {S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U : S.Opens) (hU : Dense (U : Set S)) (G : Over S)
    [GrpObj G] (hG : IsSemiAbelian G) (hH : IsSemiAbelian (𝟙_ (Over S))) : Concl U G (𝟙_ (Over S)) := by
  refine concl_of_exists hS U hU G _ hG hH fun f _ => ⟨toUnit G, ?_⟩
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback U.ι))]
  exact toUnit_unique _ _

theorem isSemiAbelian_unit (S : Scheme.{0}) : IsSemiAbelian (𝟙_ (Over S)) :=
  GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.Diag.isAbelianScheme_unit S)

theorem concl_of_isEmpty (S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S] [IsEmpty S] (U : S.Opens)
    (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) : Concl U G H := by
  obtain rfl : U = ⊤ := by ext x; exact isEmptyElim x
  exact concl_top (fun x => isEmptyElim x) G H hG hH

theorem concl_field (K : Type) [Field K] (U : (Sp K).Opens) (hU : Dense (U : Set (Sp K)))
    (G H : Over (Sp K)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) : Concl U G H := by
  obtain rfl : U = ⊤ := by
    obtain ⟨y, hy⟩ := hU.nonempty
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    ext x
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim y x ▸ hy⟩
  exact concl_top (GlobalTheory.IsNormalScheme.pred _) G H hG hH

theorem not_concl_bot : ¬ Concl (⊥ : (Sp ℤ).Opens) (Gm (Sp ℤ)) (Gm (Sp ℤ)) := by
  intro h
  obtain ⟨F, -, hu⟩ := h (𝟙 _) inferInstance
  have h₁ := hu (𝟙 _) ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  have he : IsEmpty ((Over.pullback (⊥ : (Sp ℤ).Opens).ι).obj (Gm (Sp ℤ))).left :=
    ⟨fun x => (((Over.pullback (⊥ : (Sp ℤ).Opens).ι).obj (Gm (Sp ℤ))).hom x).2⟩
  have h₂ := hu 1 ⟨by rw [Hom.one_def]; infer_instance,
    Over.OverMorphism.ext ((isInitialOfIsEmpty).hom_ext _ _)⟩
  exact ((GlobalTheory.splitTorus_properties (Sp ℤ)).1 (ULift.{0} ℤ)).2.2.2.2.2.2.2.2.2.1 inferInstance inferInstance
    (h₁.trans h₂.symm)

end GlobalTheory.Published.SemiAbelianHomExtension.Edge
