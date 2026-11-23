import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum Classical

namespace UpperTheory.Gal.TranscendenceTraces

variable {R : Type} [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S)

def pbm {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') : pullback p u' ⟶ pullback p u :=
  pullback.lift (pullback.fst p u') (pullback.snd p u' ≫ g) (by rw [Category.assoc, h, pullback.condition])

@[reassoc (attr := simp)]
theorem pbm_fst {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.fst p u = pullback.fst p u' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pbm_snd {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u') :
    pbm p g u u' h ≫ pullback.snd p u = pullback.snd p u' ≫ g := pullback.lift_snd _ _ _

abbrev DS (G : Shv R) (U : Scheme.{0}) : Type 1 := ⨁ u : (U ⟶ S), Sec G (pullback p u)

def inc (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) : Sec G (pullback p u) →ₗ[ULift.{1} R] DS p G U :=
  DirectSum.lof (ULift.{1} R) (U ⟶ S) (fun u => Sec G (pullback p u)) u

theorem DS.hom_ext {G : Shv R} {U : Scheme.{0}} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f f' : DS p G U →ₗ[ULift.{1} R] M} (h : ∀ u a, f (inc p G u a) = f' (inc p G u a)) : f = f' :=
  DirectSum.linearMap_ext _ fun u => LinearMap.ext fun a => h u a

theorem inc_congr (G : Shv R) {U : Scheme.{0}} {u u' : U ⟶ S} (h : u' = u) (k : pullback p u' ⟶ pullback p u)
    (h1 : k ≫ pullback.fst p u = pullback.fst p u') (h2 : k ≫ pullback.snd p u = pullback.snd p u')
    (a : Sec G (pullback p u)) : inc p G u' (Sec.res k a) = inc p G u a := by
  subst h
  have : k = 𝟙 _ := pullback.hom_ext (by simpa using h1) (by simpa using h2)
  rw [this, res_id]

def DS.res (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) : DS p G U →ₗ[ULift.{1} R] DS p G U' :=
  DirectSum.toModule _ _ _ fun u => inc p G (g ≫ u) ∘ₗ (G.obj.map (pbm p g u _ rfl).op).hom

theorem DS.res_inc (G : Shv R) {U' U : Scheme.{0}} (g : U' ⟶ U) (u : U ⟶ S) (u' : U' ⟶ S) (h : g ≫ u = u')
    (a : Sec G (pullback p u)) : DS.res p G g (inc p G u a) = inc p G u' (Sec.res (pbm p g u u' h) a) := by
  subst h
  exact DirectSum.toModule_lof _ _ _

def DS.map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] DS p G' U :=
  DirectSum.toModule _ _ _ fun u => inc p G' u ∘ₗ (f.hom.app (op (pullback p u))).hom

theorem DS.map_inc {G G' : Shv R} (f : G ⟶ G') {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    DS.map p f U (inc p G u a) = inc p G' u (Sec.map f a) := DirectSum.toModule_lof _ _ _

def phiP (G : Shv R) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (DS p G U.unop)
  map g := ModuleCat.ofHom (DS.res p G g.unop)
  map_id U := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (𝟙 _) (inc p G u a) = inc p G u a
    rw [DS.res_inc p G _ u _ rfl]
    exact inc_congr p G (Category.id_comp u) _ (by simp) (by simp) a)
  map_comp f g := ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.res p G (g.unop ≫ f.unop) (inc p G u a) = DS.res p G g.unop (DS.res p G f.unop (inc p G u a))
    rw [DS.res_inc p G _ u _ (Category.assoc _ _ _), DS.res_inc p G f.unop u _ rfl, DS.res_inc p G g.unop _ _ rfl, res_res]
    congr 2
    exact pullback.hom_ext (by simp) (by simp))

def phiPF (R : Type) [CommRing R] : Shv R ⥤ (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) where
  obj G := phiP p G
  map {G G'} f :=
    { app := fun U => ModuleCat.ofHom (DS.map p f U.unop)
      naturality := fun U V g => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
        change DS.map p f _ (DS.res p G g.unop (inc p G u a)) = DS.res p G' g.unop (DS.map p f _ (inc p G u a))
        rw [DS.res_inc p G _ u _ rfl, DS.map_inc, DS.map_inc, DS.res_inc p G' _ u _ rfl, map_res]) }
  map_id G := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => DS.map_inc p (𝟙 G) u a))
  map_comp {G G' G''} f g := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f ≫ g) _ (inc p G u a) = DS.map p g _ (DS.map p f _ (inc p G u a))
    rw [DS.map_inc, DS.map_inc, DS.map_inc]
    rfl))

instance (R : Type) [CommRing R] : (phiPF p R).Additive where
  map_add {G G' f g} := NatTrans.ext (funext fun U => ModuleCat.hom_ext (DS.hom_ext p fun u a => by
    change DS.map p (f + g) _ (inc p G u a) = DS.map p f _ (inc p G u a) + DS.map p g _ (inc p G u a)
    rw [DS.map_inc, DS.map_inc, DS.map_inc, ← map_add]
    rfl))

def phi (R : Type) [CommRing R] : Shv R ⥤ Shv R := phiPF p R ⋙ presheafToSheaf _ _

instance (R : Type) [CommRing R] : (phi p R).Additive := by
  unfold phi
  infer_instance

def phiSec (G : Shv R) (U : Scheme.{0}) : DS p G U →ₗ[ULift.{1} R] Sec ((phi p R).obj G) U :=
  ((toSheafify Scheme.etaleTopology (phiP p G)).app (op U)).hom

theorem phiSec_res (G : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (x : DS p G U) :
    Sec.res g (phiSec p G U x) = phiSec p G V (DS.res p G g x) :=
  (congrArg (fun h => h.hom x) ((toSheafify Scheme.etaleTopology (phiP p G)).naturality g.op)).symm

theorem phiSec_map {G G' : Shv R} (f : G ⟶ G') (U : Scheme.{0}) (x : DS p G U) :
    Sec.map ((phi p R).map f) (phiSec p G U x) = phiSec p G' U (DS.map p f U x) :=
  (congrArg (fun h => (h.app (op U)).hom x) (toSheafify_naturality Scheme.etaleTopology ((phiPF p R).map f))).symm

def Sq.cmp {p : Z ⟶ S} (A : Sq p) : pullback p A.u ⟶ A.V :=
  A.pb.lift (pullback.fst p A.u) (pullback.snd p A.u) pullback.condition

@[reassoc (attr := simp)]
theorem Sq.cmp_v {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.v = pullback.fst p A.u := A.pb.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Sq.cmp_r {p : Z ⟶ S} (A : Sq p) : A.cmp ≫ A.r = pullback.snd p A.u := A.pb.lift_snd _ _ _

def phiE (G : Shv R) : Fam0 p G ((phi p R).obj G) where
  app A := (phiSec p G A.U ∘ₗ inc p G A.u ∘ₗ (G.obj.map A.cmp.op).hom).toAddMonoidHom
  nat {A B} t a := by
    change Sec.res t.g (phiSec p G B.U (inc p G B.u (Sec.res B.cmp a))) =
      phiSec p G A.U (inc p G A.u (Sec.res A.cmp (Sec.res t.k a)))
    rw [phiSec_res, DS.res_inc p G t.g B.u A.u t.hu, res_res, res_res]
    congr 3
    exact B.pb.hom_ext (by simp [t.hv]) (by simp [t.hr])

theorem phiE_app (G : Shv R) (A : Sq p) (a : Sec G A.V) :
    (phiE p G).app A a = phiSec p G A.U (inc p G A.u (Sec.res A.cmp a)) := rfl

theorem phiE_of (G : Shv R) {U : Scheme.{0}} (u : U ⟶ S) (a : Sec G (pullback p u)) :
    (phiE p G).app (Sq.of p u) a = phiSec p G U (inc p G u a) := by
  refine (phiE_app p G (Sq.of p u) a).trans ?_
  exact congrArg _ (inc_congr p G rfl _ (Sq.cmp_v (Sq.of p u)) (Sq.cmp_r (Sq.of p u)) a)

end UpperTheory.Gal.TranscendenceTraces

end
