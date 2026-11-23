import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafVan0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) : pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s :=
  pullback.fst _ _

def LeafVanStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
    Subsingleton (Hrel (ZMod q) (sch.map (prS p ι (t ≫ U.hom))) (tw q i) m)) →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafVanW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → (∃ x : Sp A, (∀ z : Sp A, z ⤳ x) ∧ s x ∈ Set.range ι) →
  ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafVanV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y S : Scheme.{0}} (ι : W ⟶ B) (p : Y ⟶ B) (s : S ⟶ B),
  (∀ x : S, s x ∉ Set.range ι) → ∀ m : ℤ, Subsingleton (Ht q (sch.obj (pullback p s)) m i) →
  Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

theorem LeafVan0_of (hS : LeafVanStalk) (hW : LeafVanW) (hV : LeafVanV) : LeafVan0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV' p g1 g2 hp _ _ hSHV U m hm y
  refine hS hH q k hq i b ι p hp U m ?_ y
  intro A _ t hA
  obtain ⟨hHen, _⟩ := hA
  by_cases hx : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ Set.range ι
  · exact hW hH q k hq i b ι p hp A (t ≫ U.hom) ⟨hHen, ‹_›⟩
      ⟨IsLocalRing.closedPoint A, fun z => IsLocalRing.specializes_closedPoint z, hx⟩ m
  · have hall : ∀ z : Sp A, (t ≫ U.hom) z ∈ (V : Set B) := by
      intro z
      have hz : (t ≫ U.hom) z ⤳ (t ≫ U.hom) (IsLocalRing.closedPoint A) :=
        (IsLocalRing.specializes_closedPoint z).map (t ≫ U.hom).continuous
      have hxV : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ (V : Set B) := by rw [hV']; exact hx
      exact hz.mem_open V.isOpen hxV
    have hrange : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) := by rintro _ ⟨z, rfl⟩; exact hall z
    have hmiss : ∀ z : Sp A, (t ≫ U.hom) z ∉ Set.range ι := by
      intro z hz; have := hall z; rw [hV'] at this; exact this hz
    exact hV hH q i ι p (t ≫ U.hom) hmiss m ((hSHV A (t ≫ U.hom) ⟨hHen, ‹_›⟩ hrange).1 m (by omega))

end LateralTheory.E.LeafVan0Pf
