import Development.EtaleCohomology.WeilConjectures.LerayCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut

namespace LateralTheory.EWeil.PushPf

abbrev bmap {A B : CommRingCat.{0}} (β : A ⟶ B) {W' W : (Spec A).Etale} (g : W' ⟶ W) :
    pullback W'.hom (Spec.map β) ⟶ pullback W.hom (Spec.map β) :=
  pullback.map _ _ _ _ g.left (𝟙 _) (𝟙 _) (by simp [MorphismProperty.Over.w g]) (by simp)

def LocCls (q : ℕ) {A B : CommRingCat.{0}} (β : A ⟶ B) (i : ℤ) (F : Sm A) (m : ℕ) : Prop :=
  ∀ (V : (Spec A).Etale) (s : F.obj.obj (op V)) (v : V.left),
    ∃ (W : (Spec A).Etale) (g : W ⟶ V) (w : W.left), g.left w = v ∧
      ∃ c : Ht q (sch.obj (pullback W.hom (Spec.map β))) (m : ℤ) i,
        ∀ (W' : (Spec A).Etale) (g' : W' ⟶ W) (w' : W'.left), g'.left w' = w →
          pull _ (sch.map (bmap β g')) _ _ c = 0 →
          ∃ (W'' : (Spec A).Etale) (g'' : W'' ⟶ W') (w'' : W''.left), g''.left w'' = w' ∧
            (F.obj.map (g'' ≫ g' ≫ g).op).hom s = 0

def PushCx : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) → ∀ i : ℤ,
  ∃ K : CochainComplex (Sm A) ℕ,
    (∀ s n : ℕ, 0 < n → Subsingleton (Sheaf.H.{1} (K.X s) n)) ∧
    (∀ (m : ℕ) (V : (Spec A).Etale) (x : (K.homology m).obj.obj (op V)), q • x = 0) ∧
    (∀ m : ℕ, LocCls q β i (K.homology m) m) ∧
    ∀ n : ℕ, Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) K).homology n)

def StalkLoc : Prop := Base → SHz → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) →
  ∀ (i : ℤ) (m : ℕ) (p : PrimeSpectrum A),
    (∀ (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D), IsStalk f p → IsPushout β f u v → Van q D m) →
    ∀ (W : (Spec A).Etale) (w : W.left), W.hom w = p →
      ∀ c : Ht q (sch.obj (pullback W.hom (Spec.map β))) (m : ℤ) i,
        ∃ (W' : (Spec A).Etale) (g' : W' ⟶ W) (w' : W'.left), g'.left w' = w ∧
          pull _ (sch.map (bmap β g')) _ _ c = 0

end LateralTheory.EWeil.PushPf
