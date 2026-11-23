import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.HTSympCover

theorem isSympLev_of_sympCond_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  intro p _ D R _ b N h M S t o T t₁ o' m lv' lv hα hlv
  obtain ⟨hadd, hkill, hgeo⟩ := hlv
  obtain ⟨ρ, eρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over T.left))
  let j : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, ρ (lv' a) = j ≫ lv a := fun a => Over.OverMorphism.ext (by simp [eρ, hα, j])
  have dg := GlobalTheory.SiegelPull.diag_iso m.sq m.pol
  refine ⟨fun a c => ρ.injective ?_, fun a => ρ.injective ?_, fun k _ _ x β z hx hz => ?_⟩
  · rw [map_mul, key, key, key, hadd, MonObj.comp_mul]
  · rw [map_pow, key, ← MonObj.comp_pow, hkill, MonObj.comp_one, map_one]
  obtain ⟨hker, honto, hw⟩ := hgeo k x β z hx hz
  obtain ⟨σ, eσ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk x)
  have key' : ∀ a, σ (toUnit (Over.mk x) ≫ lv' a) = (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a :=
    fun a => Over.OverMorphism.ext (by
      rw [eσ, Over.comp_left, Category.assoc, hα, Over.comp_left]
      congr 1)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a c => ?_⟩
  · rw [← hker a, ← key', map_eq_one_iff _ σ.injective]
  · obtain ⟨a, ha⟩ := honto (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σ.injective (by rw [key', ha])⟩
  · exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A T.hom m.φ _ _ (pull_isLB o.isLB _)
      (pull_isLB o'.isLB _) m.cart dg (Over.mk x) M _ _ _ _ _ (eσ _) (eσ _)).2 (by rw [key', key']; exact hw a c)

end GlobalTheory.HTSympCover
