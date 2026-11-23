import Development.EtaleCohomology.EtaleSheaves.LeafKunnethCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.LeafKunnethCut

namespace LateralTheory.E.LeafKunGlobalCut

def LeafKunFT : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  (∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b) →
  ∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s],
    KunAt q s r S deg j b

def LeafKunAffine : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s],
    KunAt q s r S deg j b) →
  ∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)), KunAt q s r S deg j b

def LeafKunQcqs : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j),
  (∀ (B : Type) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)), KunAt q s r S deg j b) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p], KunAt q p r S deg j b

theorem goal_of (h1 : LeafKunFT) (h2 : LeafKunAffine) (h3 : LeafKunQcqs) : LateralTheory.E.LeafKunnethCut.LeafKunGlobal := by
  intro hB q _ k _ _ hq Y r _ _ S _ deg j b hb hSH X p _ _
  exact h3 hB q k hq r S deg j b (h2 hB q k hq r S deg j b (h1 hB q k hq r S deg j b hb hSH)) p

end LateralTheory.E.LeafKunGlobalCut
