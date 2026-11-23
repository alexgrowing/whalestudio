import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models.RankZero

namespace GlobalTheory.LevelMapsAnyRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def unitSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

theorem levelMaps_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  have hsub := subsingleton_La hD
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (levelFieldIncl hA) :=
    ⟨(Xo₂.s ≫ spMap (levelFieldIncl hA)) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  have haut : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g => by
    obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
    exact ⟨Category.id_comp _, ν, fun _ => sec_comm hG₂ ν.cart.1.w _ _, fun _ => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, levelFieldIncl hA, m, coe_levelFieldIncl hA, hr, fun _ => sec_comm hG m.cart.1.w _ _,
    fun _ => sec_comm hG m.cart.1.w _ _, fun g _ => ⟨Iso.refl _, haut g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp (levelFieldIncl hA) =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact coe_levelFieldIncl hA x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, pullback.condition_assoc, Category.assoc, GlobalTheory.Models.RankZero.spMap_comp,
      GlobalTheory.Models.RankZero.spMap_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have i₀ : IsIso (spMap (IntermediateField.inclusion hc.le).toRingHom) := by
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 ⟨IntermediateField.inclusion_injective hc.le,
        fun x => ⟨⟨x.1, hc.ge x.2⟩, rfl⟩⟩
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom)))
  have i₁ : IsIso (pullback.lift _ _ w) := IsIso.of_isIso_fac_right e₂
  refine ⟨pullback.lift _ _ w, e₁, e₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ⟨?_, ?_⟩⟩
  · obtain rfl := (cancel_mono _).1 h
    exact ⟨unitSim D, Iso.refl _, ⟨by simp [unitSim], fun a => by rw [Subsingleton.elim (_ - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩, haut _, Category.id_comp _,
      congrArg (y ≫ ·) (Category.comp_id _).symm⟩
  · intro g _ _ _ _
    exact ⟨fun a => by rw [Subsingleton.elim (g.f l₂.M a - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩

theorem levelMaps (D : Datum H) : ToroidalLevelCompatibility (H := H) (D := D) := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · exact levelMaps_rank_zero h
  · exact (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h).1

end GlobalTheory.LevelMapsAnyRank
