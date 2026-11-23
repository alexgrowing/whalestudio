import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

abbrev TT (s : X ⟶ Sp R) : Type 1 := (IsTriv s).FullSubcategory

theorem π_bij (T : TT s) : Function.Bijective T.obj.π := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, T.obj.surj⟩
  have h := (T.obj.ker b).1 hb
  rw [T.property] at h
  exact Ideal.mem_bot.1 h

def πe (T : TT s) : T.obj.B ≃+* T.obj.B₀ := RingEquiv.ofBijective T.obj.π (π_bij T)

def pt (T : TT s) : Sp T.obj.B ⟶ X := spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) ≫ T.obj.x

theorem pt_w (T : TT s) : pt T ≫ s = algStr R T.obj.B := by
  rw [pt, Category.assoc, T.obj.w, ← spMap_comp]
  congr 1
  ext r
  exact (πe T).symm_apply_apply (algebraMap R T.obj.B r)

abbrev affF (s : X ⟶ Sp R) : AffOp X ⥤ TT s :=
  ptFunctor (F := OAff s) (fun U ↦ affPt s U.unop) (fun U ↦ affPt_w s U.unop)
    fun _ _ a ↦ affPt_res s (leOfHom a.unop)

abbrev thk (T : TT s) (p : Pair (pt T)) : TT s :=
  ⟨Thick.triv (Sec (algStr R T.obj.B) p.1.1.1) (affPt _ p.1.1 ≫ pt T)
    (by rw [Category.assoc, pt_w]; exact affPt_w _ p.1.1), rfl⟩

def secPullA (T : TT s) (p : Pair (pt T)) : Sec s p.1.2.1 →ₐ[R] Sec (algStr R T.obj.B) p.1.1.1 :=
  { secPull s (algStr R T.obj.B) p with
    commutes' := (semiHom_secPull (σ := RingHom.id R)
      (by rw [spMap_id, Category.comp_id, pt_w]) p).map_algebraMap }

def aM (T : TT s) (p : Pair (pt T)) : (affF s).obj (op p.1.2) ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (secPullA T p) (secPull_affPt s _ p)⟩

theorem bM_pt (T : TT s) (p : Pair (pt T)) :
    spMap ((toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)) =
      affPt (algStr R T.obj.B) p.1.1 ≫ spMap ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
  rw [spMap_comp, affPt_eq]
  rfl

abbrev fv (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T T' : TT s} (a : T ⟶ T') : T'.obj.B := f.1 T T' a

def bM (T : TT s) (p : Pair (pt T)) : T ⟶ thk T p :=
  ⟨{ φ := toSec R T.obj.B p.1.1
     φ₀ := (toSec R T.obj.B p.1.1).toRingHom.comp ((πe T).symm : T.obj.B₀ →+* T.obj.B)
     comm := fun b ↦ congrArg (toSec R T.obj.B p.1.1) ((πe T).symm_apply_apply b)
     dp := isDPMorphism_of_eq_bot _ T.property _ _
     pt := (congrArg (· ≫ T.obj.x) (bM_pt T p)).trans (Category.assoc _ _ _) }⟩

def hSec (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)) (T : TT s) (p : Pair (pt T)) :
    Sec (algStr R T.obj.B) p.1.1.1 :=
  secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)

end GlobalTheory.CechDR.AffLoc
