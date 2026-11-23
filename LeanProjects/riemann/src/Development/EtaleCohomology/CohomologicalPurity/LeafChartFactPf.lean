import Development.EtaleCohomology.CohomologicalPurity.LeafExcPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def WVec (d : ℕ) (U : Scheme.{0}) : Type := {v : Vec (d + 1) 0 U // IsUnit (v.1 0)}

instance (d : ℕ) (U : Scheme.{0}) : SmallCategory (WVec d U) where
  Hom v w := v.1 ⟶ w.1
  id v := 𝟙 v.1
  comp f g := f ≫ g
  id_comp f := Category.id_comp (obj := Vec (d + 1) 0 U) f
  comp_id f := Category.comp_id (obj := Vec (d + 1) 0 U) f
  assoc f g h := Category.assoc (obj := Vec (d + 1) 0 U) f g h

def WVec.map (d : ℕ) {V U : Scheme.{0}} (f : V ⟶ U) : WVec d U ⥤ WVec d V where
  obj v := ⟨(Vec.map (d + 1) 0 f).obj v.1, v.2.map f.appTop.hom⟩
  map u := (Vec.map (d + 1) 0 f).map u
  map_id v := (Vec.map (d + 1) 0 f).map_id v.1
  map_comp p q := (Vec.map (d + 1) 0 f).map_comp p q

def wCat (d : ℕ) : Scheme.{0}ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (WVec d U.unop)
  map f := (WVec.map d f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def Wsp (d : ℕ) : Spc := (wCat d ⋙ nerveFunctor).flip

def WVec.incl (d : ℕ) (U : Scheme.{0}) : WVec d U ⥤ Vec (d + 1) 0 U where
  obj v := v.1
  map u := u

def Wincl (d : ℕ) : Wsp d ⟶ Pj (d + 1) 0 :=
  nerveMap { app := fun U => (WVec.incl d U.unop).toCatHom, naturality := fun _ _ _ => rfl }

def Wpt {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : sch.obj X ⟶ Wsp d where
  app n :=
    { app := fun U => TypeCat.ofHom fun (f : U.unop ⟶ X) =>
        (Functor.const (Fin (n.unop.len + 1))).obj ((WVec.map d f).obj v)
      naturality := fun U U' g => by
        ext f
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact ((WVec.map d g.unop).map_id ((WVec.map d f).obj v)).symm }
  naturality n m f := rfl

theorem wpt_incl {d : ℕ} {X : Scheme.{0}} (v : WVec d X) : Wpt v ≫ Wincl d = Pj.pt v.1 := rfl

def wvec1 {d : ℕ} {A : Type} [CommRing A] (x : Fin d → A) : WVec d (Spec (CommRingCat.of A)) :=
  ⟨vec1 x, by
    show IsUnit ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0))
    rw [Fin.cons_zero, map_one]; exact isUnit_one⟩

abbrev W (d : ℕ) (R : Type) [CommRing R] : Spc := Wsp d ⨯ sp R

def wb (d : ℕ) (R : Type) [CommRing R] : W d R ⟶ PR (d + 1) 0 R := prod.map (Wincl d) (𝟙 _)

def wa (d : ℕ) (R : Type) [CommRing R] : sp (MvPolynomial (Fin d) R) ⟶ W d R :=
  prod.lift (Wpt (wvec1 MvPolynomial.X)) (spMap MvPolynomial.C)

theorem wa_wb (d : ℕ) (R : Type) [CommRing R] : wa d R ≫ wb d R =
    (prod.lift (Pj.pt (vec1 MvPolynomial.X)) (spMap MvPolynomial.C) :
      sp (MvPolynomial (Fin d) R) ⟶ PR (d + 1) 0 R) := by
  simp only [wa, wb, prod.lift_map, Category.comp_id, wpt_incl]
  rfl

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  have h : ∀ n, Mono ((sch.map U.ι).app n) := by
    intro n
    have : ∀ V, Mono (((sch.map U.ι).app n).app V) := by
      intro V
      rw [mono_iff_injective]
      intro f g h
      change f ≫ U.ι = g ≫ U.ι at h
      exact (cancel_mono U.ι).1 h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

def LeafWCov : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  Cover2 (ZMod q) (wb d R) (pr d R).hom

def LeafWEqvR : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∀ i, Eqv _ (wa d R) (tw q i)

def LeafWEqvL : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
  (I : Ideal (MvPolynomial (Fin d) R)), Ideal.span (Set.range MvPolynomial.X) = I → IsUnit (q : R) →
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → ∀ i, Eqv _ g (tw q i)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

namespace LateralTheory.CohomologicalPurity.Thom.ExcP

open Chart in
theorem LeafChartFact_of (hG : LeafGeo) (hC : LeafWCov) (hR : LeafWEqvR) (hL : LeafWEqvL) :
    LeafChartFact := by
  intro hH q _ d R _ I hI hq Φ hΦ
  have := hG.1 d R
  have hab : wa d R ≫ wb d R = Φ.right := by rw [hΦ, wa_wb]
  have hw : ((opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R) ≫ wb d R = Φ.left ≫ (pr d R).hom := by
    erw [Category.assoc, hab]; exact (Arrow.w Φ).symm
  let P : Arrow Spc := Arrow.mk (pullback.fst (wb d R) (pr d R).hom)
  let β : P ⟶ pr d R := Arrow.homMk (pullback.snd _ _) (wb d R) pullback.condition.symm
  let α : opn (off (MvPolynomial (Fin d) R) I) ⟶ P :=
    Arrow.homMk (pullback.lift _ _ hw) (wa d R) (pullback.lift_fst _ _ _)
  refine ⟨P, α, β, ?_, opn_mono _, (IsPullback.of_hasPullback (wb d R) (pr d R).hom).mono_fst_of_mono this,
    hL hH q d R I hI hq _ (pullback.lift_fst _ _ _), hR hH q d R hq, IsPullback.of_hasPullback _ _, hC hH q d R hq⟩
  exact hom_ext (hG.1 d R) (by rw [Arrow.comp_right]; exact hab)

end LateralTheory.CohomologicalPurity.Thom.ExcP
