import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem UpperTheory.isogeny_class_exists_of_quotient :
    QObj → QComp → QUniq → QLev → ClsEx := by
  intro hObj hComp hUniq hLev q _ D R R' _ _ _ b gb β hM N N₀ c a 𝔞 hN hpos h3 hcop hgen Y X s o
  obtain ⟨o₀, ⟨n⟩⟩ := hObj q D R R' b gb β hM N N₀ c hN hpos hcop X s o
  obtain ⟨l, hl, hln⟩ := hLev q D R R' b gb N N₀ c a 𝔞 hpos hgen X s _ o o₀ n
  obtain ⟨f, ⟨hfs, m, hm⟩, hfu⟩ := Y.rep X _ o₀ l hl
  have key : ∀ (j : X ⟶ Y.X), j ≫ Y.s = s ≫ spMap β → ∀ (k : QMap o Y.univ j c),
      (∀ y : D.La, Over.Hom.left (o.eta ((algebraMap (NumberField.RingOfIntegers D.F) D.O) a • y)) ≫ k.φ =
        j ≫ Over.Hom.left (Y.lv y)) → j = f := by
    intro j hj k hk
    obtain ⟨k', hk'⟩ : ∃ k' : QMap o Y.univ (𝟙 X ≫ j) c, k'.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ :=
      (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) j).2.2.1 inferInstance n k'
    apply hfu
    refine ⟨hj, m', fun y => ?_⟩
    rw [← hln y, Category.assoc, ← hm', hk']
    exact hk y
  obtain ⟨n', hn'⟩ := (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) f).1 n m
  refine ⟨⟨⟨𝟙 X ≫ f, by rw [Category.id_comp, hfs], n', fun y => ?_⟩⟩, ?_⟩
  · rw [hn', ← Category.assoc, hln y, hm y, Category.id_comp]
  · intro C C'
    obtain ⟨j, ov, k, hk⟩ := C
    obtain ⟨j', ov', k', hk'⟩ := C'
    have e1 := key j ov k hk
    have e2 := key j' ov' k' hk'
    subst e1
    subst e2
    exact ⟨rfl, hUniq q D R R' b gb N N₀ c h3 hcop X Y.X s Y.s o Y.univ _ k k'⟩
