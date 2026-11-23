import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH

universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatCohProd

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}

def tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) : Cn (piF F) n :=
  fun s i => g i s

theorem pull_tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) (i : ι) :
    (piProj F i).pullC n (tup F n g) = g i := rfl

theorem cochain_ext (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) {a b : Cn (piF F) n}
    (h : ∀ i, (piProj F i).pullC n a = (piProj F i).pullC n b) : a = b :=
  funext fun s => funext fun i => congrFun (h i) s

theorem pull_d (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (a : Cn (piF F) n) (i : ι) :
    (piProj F i).pullC (n + 1) (d (piF F) n a) = d (F i) n ((piProj F i).pullC n a) :=
  ((piProj F i).d_pullC n a).symm

theorem piH_bijective : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}
    (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ),
    Function.Bijective fun (x : H (piF F) n) (i : ι) => (piProj F i).pull n x := by
  intro R _ C _ ι F n
  have hz : ∀ (i : ι) (a : Cn (piF F) n), d (piF F) n a = 0 →
      d (F i) n ((piProj F i).pullC n a) = 0 := fun i a ha => by
    rw [← pull_d, ha, map_zero]
  constructor
  · intro x y hxy
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).1 y
    have hi : ∀ i, (piProj F i).pullC n a - (piProj F i).pullC n b ∈ (cx (F i)).B n := fun i => by
      have h := congrFun hxy i
      have h' : (cx (F i)).cls ((piProj F i).pullC n a) (hz i a ha) =
          (cx (F i)).cls ((piProj F i).pullC n b) (hz i b hb) := h
      exact ((CrystallineSemistableComparison.P.cls_surj (cx (F i)) n).2.2.1 _ _ _ _).1 h'
    refine ((CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).2.2.1 a b ha hb).2 ?_
    cases n with
    | zero =>
      have h0 : a - b = 0 := by
        refine cochain_ext F 0 fun i => ?_
        rw [map_sub, map_zero]
        exact hi i
      rw [h0]
      exact Submodule.zero_mem _
    | succ n =>
      have hi' : ∀ i, ∃ c : Cn (F i) n, d (F i) n c =
          (piProj F i).pullC (n + 1) a - (piProj F i).pullC (n + 1) b := hi
      choose c hc using hi'
      refine ⟨tup F n c, cochain_ext F (n + 1) fun i => ?_⟩
      change (piProj F i).pullC (n + 1) (d (piF F) n (tup F n c)) = _
      rw [pull_d, pull_tup, hc, map_sub]
  · intro y
    have hy : ∀ i, ∃ (a : Cn (F i) n) (ha : d (F i) n a = 0), y i = (cx (F i)).cls a ha :=
      fun i => (CrystallineSemistableComparison.P.cls_surj (cx (F i)) n).1 (y i)
    choose a ha e using hy
    have hd : d (piF F) n (tup F n a) = 0 := by
      refine cochain_ext F (n + 1) fun i => ?_
      rw [pull_d, pull_tup, ha, map_zero]
    refine ⟨(cx (piF F)).cls (tup F n a) hd, funext fun i => ?_⟩
    rw [e i]
    rfl

end GlobalTheory.CompanionTheory.CatCohProd
