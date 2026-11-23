import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import BuildAid.D2

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.E

open CH GlobalTheory.EtC

theorem pull_smul_cls {R' : Type} [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R'} (G : C' ⥤ C) (t : R') (y : CH.H F 2)
    (z : Cn (G ⋙ F) 2) (hz : d (G ⋙ F) 2 z = 0) (h : (Mor.restrict F G).pull 2 y = (cx (G ⋙ F)).cls z hz) :
    ∃ hz' : d (G ⋙ F) 2 (t • z) = 0, (cx (G ⋙ F)).cls (t • z) hz' = (Mor.restrict F G).pull 2 (t • y) := by
  refine ⟨by rw [map_smul, hz, smul_zero], ?_⟩
  exact ((((Mor.restrict F G).pull 2).map_smul t y).trans (congrArg (t • ·) h)).symm

theorem pull_cls {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {L : C ⥤ ModuleCat.{0} R} {F : C' ⥤ ModuleCat.{0} R'} (m : Mor L F σ) (z : Cn L 2) (hz : d L 2 z = 0) :
    ∃ hz' : d F 2 (m.pullC 2 z) = 0, m.pull 2 ((cx L).cls z hz) = (cx F).cls (m.pullC 2 z) hz' :=
  ⟨by rw [m.d_pullC, hz, map_zero], rfl⟩

theorem pull_cls' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C D T P : Type 1} [Category.{0} C] [Category.{0} D]
    [Category.{0} T] [Category.{0} P] (G : C ⥤ D) (π : D ⥤ T) (ι : T ⥤ P) (A : P ⥤ CommAlgCat.{0} R')
    {L : C ⥤ ModuleCat.{0} R} (m : Mor L (modF (((G ⋙ π) ⋙ ι) ⋙ A)) σ) (z : Cn L 2) (hz : d L 2 z = 0) (a : CH.H L 2)
    (ha : a = (cx L).cls z hz) :
    ∃ hz' : d (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2 (m.pullC 2 z) = 0,
      @Eq (CH.H (G ⋙ modF ((π ⋙ ι) ⋙ A)) 2) (m.pull 2 a) ((cx (G ⋙ modF ((π ⋙ ι) ⋙ A))).cls (m.pullC 2 z) hz') := by
  subst ha
  exact pull_cls m z hz

theorem isUnit_gb {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) : IsUnit (l : Γ(gb M, ⊤)) := by
  have h : IsUnit (l : PadicAlgCl l) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have := h.map (((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom).comp (toΓ _))
  rwa [map_natCast] at this

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {C : Type 1} [Category.{0} C]

theorem eG_cls (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (hz : d (probe H r (G ⋙ CategoryOfElements.π _) n).L 2 z = 0)
    (he : (pts H r M G n).et 1 2 x = (cx (probe H r (G ⋙ CategoryOfElements.π _) n).L).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (lcCo hN H r G n 2 z) = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls (lcCo hN H r G n 2 z) hz' :=
  pull_cls' G (CategoryOfElements.π _) (testι l) (AcrA l n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) z hz _ he

theorem tCo_cls (M : Model l K) (G : C ⥤ El M.P) (n : ℕ) (e : EtFam l K) (v : Hl l (sch.obj (gb M)) (2 : ℕ) 0)
    (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0)
    (h : (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e M n 2 (v.1 n)) = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz) :
    ∃ hz' : d (G ⋙ modF (AcrEl M.P n)) 2 (tCo G n 2 z) = 0,
      (cx (G ⋙ modF (AcrEl M.P n))).cls (tCo G n 2 z) hz' = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e.tMul M v n) :=
  pull_smul_cls G _ _ z hz h

theorem res_cls (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (G : C ⥤ El M.P) (n : ℕ)
    (x : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 1) (v : Ht (l ^ n) (sch.obj (gb M)) (2 : ℕ) 0)
    (hv : eM hN H r M n 0 2 v = eM hN H r M n 1 2 x) (y : CH.H (G ⋙ modF (AcrEl M.P n)) 2) (he : eG hN H r M G n 1 2 x = y) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (eM hN H r M n 0 2 v) = y :=
  (congrArg (fun a => (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 a) hv).trans ((h6 E hN l H r K M C G n 1 2 x).trans he)

theorem isFirstChern_of_cocycle {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l} {D : LineData X}
    {y : ∀ n, MH (PX q κ) n 2}
    (h : ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El (PX q κ)) (Λ : Lift G D) (n : ℕ),
      ∃ (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2), Λ.IsCoc n z ∧ ∃ hz : d (G ⋙ modF (AcrEl (PX q κ) n)) 2 z = 0,
        (cx (G ⋙ modF (AcrEl (PX q κ) n))).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 (y n)) :
    IsFirstChernClassOfLineBundle q κ D y := fun C _ G Λ n =>
  (h C G Λ n).elim fun z a => a.2.elim fun hz b => Exists.intro z (Exists.intro hz (And.intro a.1 b))

theorem step (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (D : LineData M.X) (D' : LineData (gb M)) (π : D'.Y ⟶ D.Y)
    (hD : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (L : cech D'.f ⟶ ofCat (glCat 1)) (hL : D'.IsMap L) (n : ℕ)
    (hI : GlobalTheory.EtC.Inv (l ^ n) (cech D'.f)) (x : Ht (l ^ n) (sch.obj (gb M)) 2 1) (hx : pull _ (cechAug D'.f) _ 2 x = c1 (l ^ n) L)
    (G : C ⥤ El M.P) (Λ : Lift G D) :
    ∃ z : Cn (G ⋙ modF (AcrEl M.P n)) 2, Λ.IsCoc n (tCo G n 2 z) ∧ ∃ hz : d (G ⋙ modF (AcrEl M.P n)) 2 z = 0,
      eG hN H r M G n 1 2 x = (cx (G ⋙ modF (AcrEl M.P n))).cls z hz := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h5 hN l H r K M D D' π hD C G Λ n).elim fun z a => a.1.elim fun k =>
    (h4 E.gen E.kum E.c1 (l ^ n) C _ (gb M) (pts H r M G n) D' L hL hI x hx z k).elim fun hz he =>
      Exists.intro (lcCo hN H r G n 2 z) (And.intro a.2 (eG_cls hN H r M G n x z hz he))

theorem firstChern_family_of_lifts (h1 : LineBC) (h2 : LineMap) (h3 : FirstChernCompatibleSystem) (h4 : EtaleFirstChernKummer) (h5 : FKum) (h6 : FRes) (h7 : FUntw) : FirstChernClassFamily :=
  fun E hN l _ H r K M D => (h1 (gb M) M.X (pullback.fst _ _ ≫ pullback.fst _ _) D).elim fun D' a => a.elim fun π hD =>
    (h2 _ D').elim fun L hL =>
      have b := @h3 E.a2 E.a11 l _ D'.Y (gb M) D'.f D'.sm D'.surj (isUnit_gb M) L
      b.2.elim fun x hx => (h7 E hN l H r K M x).elim fun v hv => Exists.intro v (isFirstChern_of_cocycle fun C _ G Λ n =>
        (step h4 h5 h6 E hN H r M D D' π hD L hL n (b.1 n) (x.1 n) (hx n) G Λ).elim fun z c => c.2.elim fun hz e2 =>
          Exists.intro (tCo G n 2 z) (And.intro c.1 (tCo_cls M G n (eFam hN H r K) v z hz
            (res_cls h6 E hN H r M G n (x.1 n) (v.1 n) (hv n) _ e2))))

end CrystallineSemistableComparison.E
