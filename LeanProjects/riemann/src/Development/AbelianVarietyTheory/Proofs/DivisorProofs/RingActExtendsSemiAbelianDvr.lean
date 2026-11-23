import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.ExtUnique

theorem ringAct_extends_semiAbelian_dvr : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G ⟶ G), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act a).left ≫ φ = φ ≫ (act' a).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ O _ act hh h1 hmul hadd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing W L
  have hq : QuasiCompact (spMap (algebraMap W L)) := ‹_›
  have hd : IsSchemeTheoreticallyDominant (spMap (algebraMap W L)) := ‹_›
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap (algebraMap W L))) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G (spMap (algebraMap W L)))
  have ext : ∀ x : O, ∃ F : G ⟶ G, (act x).left ≫ φ = φ ≫ F.left := by
    intro x
    have := hh x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG
      (a.hom ≫ act x ≫ b.hom) inferInstance
    refine ⟨F, ?_⟩
    have h₁ := pullback_map_left_fst (spMap (algebraMap W L)) F
    rw [hF, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  choose f hf using ext
  refine ⟨f, ⟨fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf⟩
  · have := hh x
    exact isMonHom_of_isGrpPullback hφ hφ (act x) (f x) (hf x)
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, h1, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, hmul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine over_hom_ext_of_isPullback hφ.1 ?_
    let φ₀ : Over.mk (A.hom ≫ spMap (algebraMap W L)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 A (act x) (act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, hadd, ← h]
    rfl

end GlobalTheory
