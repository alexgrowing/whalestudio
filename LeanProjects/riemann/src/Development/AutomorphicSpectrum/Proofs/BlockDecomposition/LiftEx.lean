import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineLift

theorem liftEx : CrystallineSemistableComparison.E.LiftEx := by
  intro l _ H O _ X q κ C _ G D
  have key : ∀ p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y,
      (∀ T, p T ≫ D.f = (G.obj T).2.1) → ∃ Λ : Lift G D, Λ.p = p := by
    intro p hp
    have hh : ∀ {T T' : C} (φ : T ⟶ T'),
        (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) ≫ D.f = p T' ≫ D.f := by
      intro T T' φ
      rw [Category.assoc, hp, hp]
      exact congrArg Subtype.val (G.map φ).2
    have ex : ∀ {T T' : C} (φ : T ⟶ T'), ∃ w : ((G.obj T').1.obj.A)ˣ,
        (G.obj T').1.obj.sharp w = (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)) := by
      intro T T' φ
      exact H.sharp _ (G.obj T').1.property (Units.map
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom.toMonoidHom
        (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)))
    exact ⟨{ p := p, hp := hp, w := fun φ => (ex φ).choose, hw := fun φ _ => (ex φ).choose_spec }, rfl⟩
  refine ⟨key, fun hE => ?_⟩
  have sec : ∀ T : C, ∃ p : Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y, p ≫ D.f = (G.obj T).2.1 := by
    intro T
    haveI := D.surj
    obtain ⟨s, hs⟩ := H.splitU _ (G.obj T).1.property (pullback D.f (G.obj T).2.1)
      (pullback.snd D.f (G.obj T).2.1) inferInstance inferInstance
    refine ⟨s ≫ pullback.fst D.f (G.obj T).2.1, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  choose p hp using sec
  obtain ⟨Λ, -⟩ := key p hp
  exact ⟨Λ⟩

end GlobalTheory.CompanionTheory.LineLift
