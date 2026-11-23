import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev YA {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) : Scheme.{0} :=
  pullback (toBY p U) t

abbrev prA {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback (pullback.snd (toBY p U) t ≫ t ≫ U.hom) ι ⟶ YA p U t :=
  pullback.fst _ _

abbrev aW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback (pullback.snd (toBY p U) t ≫ t ≫ U.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (pullback.fst (toBY p U) t) (𝟙 W) (𝟙 B)
    (by erw [Category.comp_id]; exact (pullback.condition_assoc _).symm) (by simp)

abbrev ptA (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A]
    (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prA p ι U t) (aW p ι U t) (pullback.fst (toBY p U) t) (pullback.lift_fst _ _ _).symm m

def LeafStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y ⟶ B), IsProper p → ∀ (U : B.Etale) (m : ℤ) (y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → ptA q i p ι U t m y = 0) →
  Cov U (fun _ a => rY q i p ι a m y = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (U : B.Etale) (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
  ¬ Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) → ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prA p ι U t)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1)
  (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) →
  ptA q i (g2 ≫ g1 ≫ p) ι U t 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0

end LateralTheory.E.LeafKill1Pf
