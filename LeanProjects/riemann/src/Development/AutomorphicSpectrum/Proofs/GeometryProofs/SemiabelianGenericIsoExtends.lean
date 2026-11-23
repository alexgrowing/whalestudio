import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.CommonModel

section Ext

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {A B : Over (Sp V)} [GrpObj A] [GrpObj B] {GK : Over (Sp K)} [GrpObj GK]

theorem hom_unique (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a) (g₁ g₂ : A ⟶ B) [IsMonHom g₁] [IsMonHom g₂]
    (h : a ≫ g₁.left = a ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  have hmap : (Over.pullback (spMap (algebraMap V K))).map g₂ =
      (Over.pullback (spMap (algebraMap V K))).map g₁ := by
    have L : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) =
          pullback.fst A.hom (spMap (algebraMap V K)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have R : ∀ g : A ⟶ B, ((Over.pullback (spMap (algebraMap V K))).map g).left ≫
        pullback.snd B.hom (spMap (algebraMap V K)) =
          pullback.snd A.hom (spMap (algebraMap V K)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [L, L, ← hio, Category.assoc, Category.assoc, h]
    · rw [R, R]
  obtain ⟨F, -, hu⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    ((Over.pullback (spMap (algebraMap V K))).map g₁) inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap⟩).symm

theorem hom_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ F : A ⟶ B, IsMonHom F ∧ a ≫ F.left = b := by
  obtain ⟨io, hiom, hio⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap V K))) ha
  obtain ⟨ko, -, hko⟩ := grpPullback_iso ha (isGrpPullback_pullback A (spMap (algebraMap V K)))
  obtain ⟨ko', hko'm, hko'⟩ := grpPullback_iso hb (isGrpPullback_pullback B (spMap (algebraMap V K)))
  have := hiom
  have := hko'm
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian V K A B hA hB
    (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply ha.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨F, hFm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst A.hom (spMap (algebraMap V K)) ≫ F.left =
      ((Over.pullback (spMap (algebraMap V K))).map F).left ≫
        pullback.fst B.hom (spMap (algebraMap V K)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hF, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem iso_exists (hA : IsSemiAbelian A) (hB : IsSemiAbelian B) {a : GK.left ⟶ A.left}
    {b : GK.left ⟶ B.left} (ha : IsGrpPullback GK A (spMap (algebraMap V K)) a)
    (hb : IsGrpPullback GK B (spMap (algebraMap V K)) b) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ a ≫ e.hom.left = b := by
  obtain ⟨F, hFm, hF⟩ := hom_exists V K hA hB ha hb
  obtain ⟨F', hF'm, hF'⟩ := hom_exists V K hB hA hb ha
  have := hFm
  have := hF'm
  have h₁ : F ≫ F' = 𝟙 _ := hom_unique V K hA hA ha _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF, hF', Over.id_left, Category.comp_id])
  have h₂ : F' ≫ F = 𝟙 _ := hom_unique V K hB hB hb _ _ (by
    rw [Over.comp_left, ← Category.assoc, hF', hF, Over.id_left, Category.comp_id])
  exact ⟨⟨F, F', h₁, h₂⟩, hFm, hF⟩

end Ext

end GlobalTheory.CompanionTheory.Ar.CommonModel

namespace GlobalTheory.CompanionTheory.Ar

theorem semiAbelian_commonModel : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) (x : Sp V ⟶ X) (x' : Sp V ⟶ X') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (φ' : GK.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap V K) ≫ x) φ → IsGrpPullback GK G' (spMap (algebraMap V K) ≫ x') φ' → ∃ (G₀ : Over (Sp V)) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left) (ψ' : G₀.left ⟶ G'.left) (κ : GK.left ⟶ G₀.left), IsGrpPullback G₀ G x ψ ∧ IsGrpPullback G₀ G' x' ψ' ∧ IsGrpPullback GK G₀ (spMap (algebraMap V K)) κ ∧ κ ≫ ψ = φ ∧ κ ≫ ψ' = φ' := by
  intro V K _ _ _ _ _ _ X X' x x' G G' _ _ GK _ φ φ' hG hG' hφ hφ'
  have pA := isGrpPullback_pullback G x
  have pB := isGrpPullback_pullback G' x'
  have sA : IsSemiAbelian ((Over.pullback x).obj G) := IsSemiAbelian.pullback x G hG
  have sB : IsSemiAbelian ((Over.pullback x').obj G') := IsSemiAbelian.pullback x' G' hG'

  have lift : ∀ {Y : Scheme.{0}} (y : Sp V ⟶ Y) (H : Over Y) [GrpObj H] (θ : GK.left ⟶ H.left),
      IsGrpPullback GK H (spMap (algebraMap V K) ≫ y) θ →
      ∃ κ : GK.left ⟶ ((Over.pullback y).obj H).left,
        IsGrpPullback GK ((Over.pullback y).obj H) (spMap (algebraMap V K)) κ ∧
          κ ≫ pullback.fst H.hom y = θ := by
    intro Y y H _ θ hθ
    have hp := isGrpPullback_pullback H y
    have w : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ ((Over.pullback y).obj H).hom =
        GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
    have f : (hp.1.lift θ (GK.hom ≫ spMap (algebraMap V K)) (by
      rw [hθ.1.w, Category.assoc])) ≫ pullback.fst H.hom y = θ := hp.1.lift_fst _ _ _
    exact ⟨_, hp.cancel (by rw [f]; exact hθ) w, f⟩
  obtain ⟨κ, hκ, hκφ⟩ := lift x G φ hφ
  obtain ⟨κ', hκ', hκφ'⟩ := lift x' G' φ' hφ'
  obtain ⟨e, hem, he⟩ := CommonModel.iso_exists V K sA sB hκ hκ'
  have := hem
  refine ⟨(Over.pullback x).obj G, inferInstance, pullback.fst G.hom x,
    e.hom.left ≫ pullback.fst G'.hom x', κ, pA, ?_, hκ, hκφ, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp pB).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, he, hκφ']

end GlobalTheory.CompanionTheory.Ar
