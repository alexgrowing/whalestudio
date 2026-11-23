import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem homStab_step : ∀ (k G : Type) [CommRing k] [Group G] (C₃ C₂ Z₁ C₁ Z₀ : Rep k G) (a : C₃ ⟶ C₂)
    (b : C₂ ⟶ Z₁) (ι : Z₁ ⟶ C₁) (e : C₁ ⟶ Z₀) (h : ι ≫ e = 0), (ShortComplex.mk ι e h).ShortExact →
    a ≫ b = 0 → ∀ q : ℕ, Function.Surjective (hMap b q).hom →
    Function.Exact (hMap a q).hom (hMap (b ≫ ι) q).hom → Function.Surjective (hMap e (q + 1)).hom := by
  intro k G _ _ C₃ C₂ Z₁ C₁ Z₀ a b ι e h hX hab q hb hex
  have hcomp : ∀ {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ),
      hMap (f ≫ g) n = hMap f n ≫ hMap g n :=
    fun f g n => (groupHomology.functor k G n).map_comp f g
  have hzero : hMap (0 : C₃ ⟶ Z₁) q = 0 := (groupHomology.functor k G q).map_zero _ _
  have hinj : Function.Injective (hMap ι q).hom := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := hb z
    have hy : (hMap (b ≫ ι) q).hom y = 0 := by
      rw [hcomp]
      simpa using hz
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomp, hab, hzero]
    rfl
  intro w
  have h3 := groupHomology.mapShortComplex₃_exact hX (i := q + 1) (j := q) rfl
  have hδ : (groupHomology.δ hX (q + 1) q rfl).hom w = 0 := by
    apply hinj
    rw [map_zero]
    exact (groupHomology.mapShortComplex₁ hX (i := q + 1) (j := q) rfl).moduleCat_zero_apply w
  exact (ShortComplex.moduleCat_exact_iff _).1 h3 w hδ

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
