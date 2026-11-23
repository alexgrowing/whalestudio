import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open PAlg

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

def JJ (k : Bool) (A : PAlg l) (n : ℕ) : Ideal (A.Acr n) :=
  match k with
  | false => A.Fil n 1
  | true => A.PFil n

def DD (k : Bool) (A : PAlg l) (n : ℕ) : DividedPowers (JJ k A n) :=
  match k with
  | false => A.pdFil n
  | true => A.pdPFil n

theorem fil_le (k : Bool) (A : PAlg l) (n : ℕ) : A.Fil n 1 ≤ JJ k A n := by
  cases k
  exacts [le_rfl, le_sup_right]

theorem le_pfil (k : Bool) (A : PAlg l) (n : ℕ) : JJ k A n ≤ A.PFil n := by
  cases k
  exacts [le_sup_right, le_rfl]

theorem dd_map (k : Bool) {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) : IsDPMorphism (DD k A n) (DD k A' n) (mapAcr f n) := by
  cases k
  exacts [dp_mapAcr f n, dpP_mapAcr f n]

theorem dd_red (k : Bool) (A : PAlg l) {m n : ℕ} (h : n ≤ m) : IsDPMorphism (DD k A m) (DD k A n) (A.red h) := by
  cases k
  exacts [A.dp_red h, A.dpP_red h]

theorem dd_gal (k : Bool) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    IsDPMorphism (DD k (base l) n) (DD k (base l) n) (galBase σ n) := by
  cases k
  exacts [dp_galBase σ n, dpP_galBase σ n]

theorem jj_le (k : Bool) {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) : JJ k A n ≤ (JJ k A' n).comap (mapAcr f n) :=
  Ideal.map_le_iff_le_comap.1 (dd_map k f n).1

def uJ (k : Bool) (A : PAlg l) (n : ℕ) : A.U →+* A.Acr n ⧸ JJ k A n := (Ideal.Quotient.factor (fil_le k A n)).comp (A.uToQ n)

theorem uJ_th (k : Bool) (A : PAlg l) (n : ℕ) (x : A.W) : uJ k A n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := rfl

theorem uJ_map (k : Bool) {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) :
    (Ideal.quotientMap _ (mapAcr f n) (jj_le k f n)).comp (uJ k A n) = (uJ k A' n).comp (mapU f) :=
  RingHom.ext fun x => by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (mapAcr_toAcr f n w)

variable (l) in

abbrev bs (k : Bool) (n : ℕ) : Base where
  R := (base l).Acr n
  I := JJ k (base l) n
  γ := DD k (base l) n
  t := 1
  p := l

def κb (κ : O →+* OC l) (k : Bool) (n : ℕ) : O →+* (bs l k n).R ⧸ (bs l k n).I :=
  (uJ k (base l) n).comp ((base l).oC.comp κ)

variable (F : Fn O) (κ : O →+* OC l)

def Fn.pt : PAlg l ⥤ Type where
  obj A := {y : F.Pt.obj (CommRingCat.of A.U) // F.Ov y (A.oC.comp κ)}
  map {A A'} f := TypeCat.ofHom fun y => ⟨F.Pt.map (CommRingCat.ofHom (mapU f)) y.1, by
    have e : (mapU f).comp (A.oC.comp κ) = A'.oC.comp κ := RingHom.ext fun x => mapU_oC f _
    exact e ▸ F.ov_map (CommRingCat.ofHom (mapU f)) y.2⟩
  map_id A := by
    ext y
    change F.Pt.map (CommRingCat.ofHom (mapU (𝟙 A))) y.1 = y.1
    rw [mapU_id, CommRingCat.ofHom_id, F.Pt.map_id]; rfl
  map_comp f g := by
    ext y
    change F.Pt.map (CommRingCat.ofHom (mapU (f ≫ g))) y.1 =
      F.Pt.map (CommRingCat.ofHom (mapU g)) (F.Pt.map (CommRingCat.ofHom (mapU f)) y.1)
    rw [mapU_comp, CommRingCat.ofHom_comp, F.Pt.map_comp]; rfl

theorem schFn_pt {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) : (schFn q).pt κ = PX q κ := rfl

abbrev Lc (k : Bool) (n : ℕ) : (bs l k n).Fun := F.cr (bs l k n) rfl (κb κ k n)

abbrev OcA (k : Bool) (n : ℕ) : Thick (Lc F κ k n) ⥤ CommAlgCat.{0} (Acris l) := OA (Lc F κ k n) ((base l).cris n)

abbrev Oc (k : Bool) (n : ℕ) : Thick (Lc F κ k n) ⥤ ModuleCat.{0} (Acris l) := OM (Lc F κ k n) ((base l).cris n)

abbrev Hc (k : Bool) (n j : ℕ) : Type 1 := CH.H (Oc F κ k n) j

def HcFil (k : Bool) (n r j : ℕ) : Submodule (Acris l) (Hc F κ k n j) := (pdS (Lc F κ k n) ((base l).cris n) r).img j

def gObj (k : Bool) (n : ℕ) (T : (F.pt κ).Elements) : Thick (Lc F κ k n) where
  B := T.1.Acr n
  i := mapAcr T.1.fromBase n
  J := JJ k T.1 n
  δ := DD k T.1 n
  adm := ⟨fun _ => ⟨n, T.1.pow_l_acr n⟩, fun h => absurd h (Fact.out : l.Prime).ne_zero⟩
  compat := dd_map k _ n
  α := ()
  y := ⟨(Ideal.quotientMap _ (mapAcr T.1.fromBase n) (jj_le k _ n), F.Pt.map (CommRingCat.ofHom (uJ k T.1 n)) T.2.1), by
    have e : (uJ k T.1 n).comp (T.1.oC.comp κ) =
        (Ideal.quotientMap _ (mapAcr T.1.fromBase n) (jj_le k _ n)).comp (κb κ k n) := RingHom.ext fun x =>
      ((RingHom.congr_fun (uJ_map k T.1.fromBase n) _).trans (congrArg (uJ k T.1 n) (mapU_oC _ _))).symm
    exact e ▸ F.ov_map (CommRingCat.ofHom (uJ k T.1 n)) T.2.2⟩
  inα := trivial
  w _ := rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

theorem mapAcr_fromBase {A A' : PAlg l} (f : A ⟶ A') (n : ℕ) (r : (base l).Acr n) :
    mapAcr f n (mapAcr A.fromBase n r) = mapAcr A'.fromBase n r := by rw [← mapAcr_comp, fromBase_comp]

def gE (k : Bool) (n : ℕ) : (F.pt κ).Elements ⥤ Thick (Lc F κ k n) where
  obj := gObj F κ k n
  map {T T'} f :=
    { φ := mapAcr f.1 n
      u := fun j => j.elim
      comm := mapAcr_fromBase f.1 n
      dp := dd_map k f.1 n
      hle := jj_le k f.1 n
      pt := Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r =>
          congrArg (Ideal.Quotient.mk _) (mapAcr_fromBase f.1 n r))) (by
        have h : F.Pt.map (CommRingCat.ofHom (mapU f.1)) T.2.1 = T'.2.1 := congrArg Subtype.val f.2
        change F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap _ (mapAcr f.1 n) (jj_le k f.1 n)))
          (F.Pt.map (CommRingCat.ofHom (uJ k T.1 n)) T.2.1) = F.Pt.map (CommRingCat.ofHom (uJ k T'.1 n)) T'.2.1
        rw [← h, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          uJ_map]))
      hx := fun j => j.elim
      hs := by
        change (1 : (T'.1.Acr n)ˣ) = (∏ j : Empty, _) * Units.map _ 1
        rw [Finset.prod_of_isEmpty, map_one, mul_one]
      hv := fun j => j.elim }
  map_id T := Thick.Hom.ext (RingHom.ext (mapAcr_id n)) (funext fun j => j.elim)
  map_comp f g := Thick.Hom.ext (RingHom.ext (mapAcr_comp f.1 g.1 n)) (funext fun j => j.elim)

def jE (P : PAlg l ⥤ Type) : El P ⥤ P.Elements where
  obj T := ⟨T.1.obj, T.2⟩
  map f := ⟨f.1.hom, f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance (P : PAlg l ⥤ Type) : (jE P).Full := ⟨fun f => ⟨⟨ObjectProperty.homMk f.1, f.2⟩, rfl⟩⟩

instance (P : PAlg l ⥤ Type) : (jE P).Faithful :=
  ⟨fun h => Subtype.ext (ObjectProperty.hom_ext _ (congrArg Subtype.val h))⟩

abbrev gT (k : Bool) (n : ℕ) : El (F.pt κ) ⥤ Thick (Lc F κ k n) := jE (F.pt κ) ⋙ gE F κ k n

def idLin {Λ B : Type} [CommRing Λ] [CommRing B] (f g : Λ →+* B) (h : ∀ a, f a = g a) :
    @LinearMap Λ Λ _ _ (RingHom.id Λ) B B _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra) (@Algebra.toModule _ _ _ _ g.toAlgebra) :=
  @LinearMap.mk Λ Λ _ _ (RingHom.id Λ) B B _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra) (@Algebra.toModule _ _ _ _ g.toAlgebra)
    ⟨fun z => z, fun _ _ => rfl⟩ fun a z => congrArg (· * z) (h a)

theorem idLin_apply {Λ B : Type} [CommRing Λ] [CommRing B] (f g : Λ →+* B) (h : ∀ a, f a = g a) (z : B) : idLin f g h z = z := rfl

def βMor (k : Bool) (n : ℕ) : CH.Mor (Oc F κ k n) (CH.modF (AcrEl (F.pt κ) n)) (RingHom.id _) where
  G := gT F κ k n
  τ T := idLin ((mapAcr T.1.obj.fromBase n).comp ((base l).cris n)) (T.1.obj.cris n) (mapAcr_cris T.1.obj.fromBase n)
  nat _ _ := rfl

def β (k : Bool) (n j : ℕ) : Hc F κ k n j →ₗ[Acris l] MH (F.pt κ) n j := (βMor F κ k n).pull j

variable {F} {F' : Fn O}

structure Fn.Map (F F' : Fn O) where
  u : F.Pt ⟶ F'.Pt
  ov : ∀ {B : CommRingCat.{0}} {y : F.Pt.obj B} {f : O →+* B}, F.Ov y f → F'.Ov (u.app B y) f

def schMap {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {q : Y ⟶ Spec (CommRingCat.of O)} (u : X ⟶ Y) (hu : u ≫ q = p) :
    Fn.Map (schFn p) (schFn q) where
  u := { app := fun B => TypeCat.ofHom fun y => y ≫ u
         naturality := fun B B' φ => by
           ext y
           exact Category.assoc _ _ _ }
  ov {B y f} h := by
    change (y ≫ u) ≫ q = _
    rw [Category.assoc, hu]; exact h

def Fn.Map.ptK (u : Fn.Map F F') {k : Type} [CommRing k] (κ₀ : O →+* k) : F.ptK κ₀ ⟶ F'.ptK κ₀ where
  app B := TypeCat.ofHom fun z => ⟨(z.1.1, u.u.app B z.1.2), u.ov z.2⟩
  naturality B B' φ := by
    ext z
    have h := ConcreteCategory.congr_hom (u.u.naturality φ) z.1.2
    exact Subtype.ext (Prod.ext rfl h)

def Fn.Map.pt (u : Fn.Map F F') : F.pt κ ⟶ F'.pt κ where
  app A := TypeCat.ofHom fun y => ⟨u.u.app _ y.1, u.ov y.2⟩
  naturality A A' f := by
    ext y
    have h := ConcreteCategory.congr_hom (u.u.naturality (CommRingCat.ofHom (mapU f))) y.1
    exact Subtype.ext h

theorem schMap_pt {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {q : Y ⟶ Spec (CommRingCat.of O)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : (schMap u hu).pt κ = pxMap κ u hu := rfl

end CrystallineSemistableComparison.B
