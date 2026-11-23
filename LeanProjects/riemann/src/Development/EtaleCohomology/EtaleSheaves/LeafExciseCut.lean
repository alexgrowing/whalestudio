import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.E8.ExciseCut

def relMap (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) (i n : ℤ) :
    HK (ZMod q) (mappingCone ((chains _).map (sch.map ι))) (tw q i) n →+
      HK (ZMod q) (mappingCone ((chains _).map (sch.map ι'))) (tw q i) n :=
  HK.pull (ZMod q) (mappingCone.map ((chains _).map (sch.map ι')) ((chains _).map (sch.map ι))
    ((chains _).map (sch.map g)) ((chains _).map (sch.map f)) (by simp only [← Functor.map_comp, w])) (tw q i) n

def relMapBC (q : ℕ) {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z) (f : X' ⟶ X)
    (w : ι' ≫ f = g ≫ ι) {T : Scheme.{0}} (s : T ⟶ X) (i n : ℤ) :=
  relMap q (pullback.map (ι' ≫ f) s f s ι' (𝟙 T) (𝟙 X) (by simp) (by simp)) (pullback.snd ι s)
    (pullback.map (ι' ≫ f) s ι s g (𝟙 T) (𝟙 X) (by simp [w]) (by simp)) (pullback.snd f s) (by rw [pullback.lift_snd, pullback.lift_snd]) i n

def LeafConeZero : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R φ F n)) → ∀ n, Subsingleton (HK R (mappingCone φ) F n)

def LeafConeFive : Prop := ∀ (R : Type) [CommRing R] {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) (F : Shv R),
  (∀ n, Function.Bijective (HK.pull R a F n)) → (∀ n, Function.Bijective (HK.pull R b F n)) →
  ∀ n, Function.Bijective (HK.pull R (mappingCone.map φ₁ φ₂ a b comm) F n)

def ExcisionRelationSquare : Prop := Base → ∀ (q : ℕ) [NeZero q] {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (g : Z' ⟶ Z)
  (f : X' ⟶ X) (w : ι' ≫ f = g ≫ ι) [QuasiCompact f] [QuasiSeparated f] [QuasiCompact ι] [QuasiSeparated ι]
  [QuasiCompact ι'] [QuasiSeparated ι'], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ n,
    Function.Bijective (relMapBC q ι' ι g f w s i n)) →
  ∀ n, Function.Bijective (relMap q ι' ι g f w i n)

def LeafExciseLocal : Prop := Base → ∀ (q : ℕ) [NeZero q] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [IsProper f]
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsUnit (q : Γ(X, ⊤)) → ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
  IsIso (f ∣_ U) → ∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ X), SH A → ∀ i n : ℤ,
  Function.Bijective (relMapBC q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition s i n)

theorem goal_of (h1 : ExcisionRelationSquare) (h2 : LeafExciseLocal) : EtaleExcise := by
  intro base q _ X' X Z _ f _ ι _ hq U hU hiso n i
  exact h1 base q (pullback.fst f ι) ι (pullback.snd f ι) f pullback.condition hq i
    (fun A _ s hA m => h2 base q f ι hq U hU hiso A s hA i m) n

end LateralTheory.E.E8.ExciseCut
