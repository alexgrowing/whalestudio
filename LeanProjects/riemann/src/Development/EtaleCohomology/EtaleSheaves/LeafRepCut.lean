import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtaleTopologySheaves
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

abbrev EtTop (B : Scheme.{0}) : GrothendieckTopology B.Etale := Scheme.smallEtaleTopology B

abbrev SShv (B : Scheme.{0}) (q : ℕ) : Type 2 := Sheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))

instance (B : Scheme.{0}) (q : ℕ) : HasSheafify (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  infer_instance

instance (B : Scheme.{0}) (q : ℕ) : IsGrothendieckAbelian.{1} (SShv B q) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

noncomputable instance (B : Scheme.{0}) (q : ℕ) : HasDerivedCategory.{2} (SShv B q) := HasDerivedCategory.standard _

def OU (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ DerivedCategory (SShv B q) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q))) ⋙ presheafToSheaf (EtTop B) _ ⋙
    DerivedCategory.singleFunctor (SShv B q) 0

def top (B : Scheme.{0}) : B.Etale := MorphismProperty.Over.mk ⊤ (𝟙 B) (inferInstanceAs (Etale (𝟙 B)))

abbrev YU {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : Scheme.{0} := pullback p U.hom

abbrev prU {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ YU p U :=
  pullback.fst _ _

abbrev resY {Y B : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : YU p U' ⟶ YU p U :=
  pullback.map p U'.hom p U.hom (𝟙 Y) a.left (𝟙 B) (by simp) (by simpa using a.w.symm)

abbrev resYW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    pullback (pullback.snd p U'.hom ≫ U'.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (resY p a) (𝟙 W) (𝟙 B)
    (by
      have h : U'.hom = a.left ≫ U.hom := by simpa using a.w.symm
      simp only [resY, pullback.lift_snd_assoc]
      exact congrArg (fun t => pullback.snd p U'.hom ≫ t) h) (by simp)

abbrev prB {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) : pullback U.hom ι ⟶ U.left := pullback.fst _ _

abbrev toBY {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : YU p U ⟶ U.left := pullback.snd _ _

abbrev toBW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ (toBY p U) (𝟙 W) (𝟙 B) (by simp) (by simp)

abbrev mY {Y Y' B : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (U : B.Etale) : YU (g ≫ p) U ⟶ YU p U :=
  pullback.map (g ≫ p) U.hom p U.hom g (𝟙 _) (𝟙 B) (by simp) (by simp)

abbrev mW {Y Y' B W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd (g ≫ p) U.hom ≫ U.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (mY p g U) (𝟙 W) (𝟙 B) (by simp only [mY, pullback.lift_snd_assoc]; simp only [Functor.id_obj, Category.comp_id]; exact Category.comp_id _) (by simp)

variable (q : ℕ) (i : ℤ)

abbrev LocE {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def Rep {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) (e : LocE q i p ι K) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n y,
    e U' n (rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm n y) =
      (OU B q).map a ≫ e U n y

abbrev LocEB {B W : Scheme.{0}} (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def MorRep {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) {K K' : DerivedCategory (SShv B q)}
    (e : LocE q i p ι K) (e' : LocE q i (g ≫ p) ι K') (f : K ⟶ K') : Prop :=
  ∀ U n y, e' U n (rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm n y) =
    e U n y ≫ (shiftFunctor _ n).map f

def MorRepB {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {L K : DerivedCategory (SShv B q)}
    (eL : LocEB q i ι L) (e : LocE q i p ι K) (ℓ : L ⟶ K) : Prop :=
  ∀ U n c, e U n (rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm n c) =
    eL U n c ≫ (shiftFunctor _ n).map ℓ

abbrev resBW {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : pullback U'.hom ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ a.left (𝟙 W) (𝟙 B) (by simpa using a.w.symm) (by simp)

def RepB {B W : Scheme.{0}} (ι : W ⟶ B) (L : DerivedCategory (SShv B q)) (e : LocEB q i ι L) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n c,
    e U' n (rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm n c) =
      (OU B q).map a ≫ e U n c

open CategoryTheory.Limits in

def LeafCons : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

def LeafDeg : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
    MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K0)) ∧
    (DerivedCategory.homologyFunctor (SShv B q) 2).map f = 0 ∧ (DerivedCategory.homologyFunctor (SShv B q) 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor (SShv B q) 0).map ℓ)

theorem goal_of (hC : LeafCons) (hD : LeafDeg) : LateralTheory.E.LeafGhostRelCut.LeafRep := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, hinj, hsurj, c0, cL⟩ :=
    hC q i ι p g1 g2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ :=
    hD hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨SShv B q, inferInstance, inferInstance, inferInstance, (OU B q).obj (top B), K0, K1, K2, L, f, g, ℓ, e0, e2, eL,
    d1, d2, d3, d4, d5, d6, hinj, hsurj, c0, cL⟩

end LateralTheory.E.EtaleTopologySheaves
