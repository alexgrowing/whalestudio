import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostRelCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

def LeafTrunc : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [HasDerivedCategory.{2} A]
  (K0 K1 K2 L : DerivedCategory A) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2),
  (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) →
  (DerivedCategory.homologyFunctor A 2).map f = 0 → (DerivedCategory.homologyFunctor A 1).map g = 0 →
  (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) →
  (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) →
  IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) →
  ∃ h : K0 ⟶ L, h ≫ ℓ = f ≫ g

def LeafRep : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∃ (A : Type 2) (_ : Category.{1} A) (_ : Abelian A) (_ : HasDerivedCategory.{2} A) (O K0 K1 K2 L : DerivedCategory A)
    (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj L)),
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) ∧
    (DerivedCategory.homologyFunctor A 2).map f = 0 ∧ (DerivedCategory.homologyFunctor A 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map ℓ)

theorem goal_of (hT : LeafTrunc) (hR : LeafRep) : LeafGhostRel := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n y
  obtain ⟨A, _, _, _, O, K0, K1, K2, L, f, g, ℓ, e0, e2, eL, hK0, hf, hg, hK2, hL, hℓ, hinj, hsurj, n0, nL⟩ :=
    hR hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨h, hh⟩ := hT A K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  obtain ⟨c, hc⟩ := hsurj n (e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map h)
  refine ⟨c, hinj n ?_⟩
  rw [n0, nL, hc, Category.assoc, ← Functor.map_comp, hh]

end LateralTheory.E.LeafGhostRelCut

end
