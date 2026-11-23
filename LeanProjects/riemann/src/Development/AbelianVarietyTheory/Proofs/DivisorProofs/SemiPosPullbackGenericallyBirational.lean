import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemiPullBir

theorem exists_isIso_restrict {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    [IsSeparated π] [LocallyOfFiniteType π] (hη : π (genericPoint Y) = genericPoint X)
    (hd : π.residueDegree (genericPoint Y) = 1) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  have hFX : IsField (X.presheaf.stalk (π (genericPoint Y))) := by
    rw [hη]
    exact Field.toIsField X.functionField
  have hFY : IsField (Y.presheaf.stalk (genericPoint Y)) := Field.toIsField Y.functionField
  have hrX : Function.Bijective (X.residue (π (genericPoint Y))).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFX.toField
    exact RingHom.injective _
  have hrY : Function.Bijective (Y.residue (genericPoint Y)).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFY.toField
    exact RingHom.injective _
  have hκ : Function.Bijective (π.residueFieldMap (genericPoint Y)).hom := by
    letI := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
    have h1 : Module.finrank (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) = 1 := hd
    refine ⟨RingHom.injective _, fun y => ?_⟩
    have htop := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    have hy : y ∈ (⊥ : Subalgebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y))) := by
      rw [htop]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
    exact ⟨a, ha⟩
  have hst : Function.Bijective (π.stalkMap (genericPoint Y)).hom := by
    have e := Scheme.residue_residueFieldMap (f := π) (genericPoint Y)
    have e' : (Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom =
        (π.residueFieldMap (genericPoint Y)).hom.comp (X.residue (π (genericPoint Y))).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← e]
    have hc : Function.Bijective ((Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom) := by
      rw [e']; exact hκ.comp hrX
    refine (Function.Bijective.of_comp_iff' hrY _).1 hc
  have : IsIso (π.stalkMap (genericPoint Y)) := (ConcreteCategory.isIso_iff_bijective _).2 hst
  let φ : Spec (X.presheaf.stalk (π (genericPoint Y))) ⟶ Y :=
    Spec.map (inv (π.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y)
  have hφ : φ ≫ π = X.fromSpecStalk (π (genericPoint Y)) ≫ 𝟙 X := by
    simp only [φ, Category.assoc, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 X) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem semiPos_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X _ p D hp Y _ q hq π hπ hη hd L hL
  have hpr : IsProper q := GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have hsep : IsSeparated (π ≫ p) := by rw [hπ]; infer_instance
  have hft : LocallyOfFiniteType (π ≫ p) := by rw [hπ]; infer_instance
  have : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  obtain ⟨U, hU, hi⟩ := exists_isIso_restrict π hη hd
  exact (GlobalTheory.SemiPosBir.semiPos_iff_pull k X Y p q D hp hq π hπ U hU hi L).1 hL

end GlobalTheory.SemiPullBir
