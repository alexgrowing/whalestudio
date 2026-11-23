import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKunnethCut

def KBasis (q : ℕ) {Y : Scheme.{0}} (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ) (b : ∀ s, Ht q (sch.obj Y) (deg s) j) :
    Prop :=
  ∀ m : ℤ, Function.Bijective fun c : {s // deg s = m} → ZMod q =>
    ∑ s : {s // deg s = m}, c s • ((b s.1).cast s.2 rfl : Ht q (sch.obj Y) m j)

def KunAt (q : ℕ) {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (r : Y ⟶ Spec (CommRingCat.of k)) (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : ∀ s, Ht q (sch.obj X) (n - deg s) i =>
    ∑ s, ((cup q (pull _ (sch.map (pullback.fst p r)) _ _ (a s)) (pull _ (sch.map (pullback.snd p r)) _ _ (b s))).cast
      (by ring) rfl : Ht q (sch.obj (pullback p r)) n (i + j))

def LeafSHCoh : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ (A : Type) [CommRing A], SH A → ∀ (_s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) (i : ℤ),
    (∃ g : Ht q (sch.obj (Spec (CommRingCat.of A))) 0 i, Function.Bijective fun c : ZMod q => c • g) ∧
    ∀ n : ℤ, n ≠ 0 → Subsingleton (Ht q (sch.obj (Spec (CommRingCat.of A))) n i)

def LeafKunLocal : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  ∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b

def LeafKunGlobal : Prop := LateralTheory.E.E8.Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (r : Y ⟶ Spec (CommRingCat.of k)) [IsProper r] [Smooth r] (S : Type) [Fintype S] (deg : S → ℤ) (j : ℤ)
    (b : ∀ s, Ht q (sch.obj Y) (deg s) j), KBasis q S deg j b →
  (∀ (A : Type) [CommRing A], SH A → ∀ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k), KunAt q s r S deg j b) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [QuasiCompact p] [QuasiSeparated p], KunAt q p r S deg j b

theorem goal_of (hL : LeafKunLocal) (hG : LeafKunGlobal) : LateralTheory.E.E8.EtaleKunneth := by
  intro hB q _ k _ _ hq X Y p r _ _ _ _ S _ deg j b hb
  exact hG hB q k hq r S deg j b hb (hL hB q k hq r S deg j b hb) p

end LateralTheory.E.LeafKunnethCut
