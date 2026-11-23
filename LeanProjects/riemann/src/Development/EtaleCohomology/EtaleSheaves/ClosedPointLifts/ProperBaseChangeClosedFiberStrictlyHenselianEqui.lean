import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafPtWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.SecondDegreeKilling

def LeafHrelZero : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E), Eqv R f F →
  ∀ n, Subsingleton (Hrel R f F n)

def LeafClosedLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (s : Sp A ⟶ B), (∃ x, s.base x ∈ Set.range ι.base) →
  ∃ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W, w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s

def ProperBaseChangeClosedFiberStrictlyHenselianEquivalence : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (s : Sp A ⟶ B), SH A →
  ∀ w : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ W,
    w ≫ ι = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s →
  Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i)

theorem LeafPtW_of (hZ : LeafHrelZero) (hL : LeafClosedLift) (hE : ProperBaseChangeClosedFiberStrictlyHenselianEquivalence) : LateralTheory.E.SecondDegreeKilling.LeafPtW := by
  intro hH q _ k _ hq i B W Y toK ι _ V hV p hp A _ s hA hs m
  obtain ⟨hh, _⟩ := hA
  have hx : ∃ x, s.base x ∈ Set.range ι.base := by
    by_contra hc
    push Not at hc
    apply hs
    rintro _ ⟨x, rfl⟩
    have : s.base x ∈ (V : Set B) := by
      rw [hV]; exact hc x
    exact this
  obtain ⟨w, hw⟩ := hL A ι s hx
  exact hZ (ZMod q) (tw q i) (sch.map (prS p ι s)) (hE hH q k hq i toK ι p hp A s ⟨hh, ‹_›⟩ w hw) m

end LateralTheory.E.LeafPtWPf
