import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem resThk_pt (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    spMap ((RingHom.id (Sec (algStr R T.obj.B) p.1.1.1)).comp
      (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) : Sec (algStr R T.obj.B) q.1.1.1 →+* Sec (algStr R T.obj.B) p.1.1.1)) ≫
      (affPt (algStr R T.obj.B) q.1.1 ≫ pt T) = affPt (algStr R T.obj.B) p.1.1 ≫ pt T := by
  rw [RingHom.id_comp, ← Category.assoc, affPt_res]

def resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) : thk T q ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq)) (resThk_pt T hpq)⟩

theorem bM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    bM T q ≫ resThk T hpq = bM T p :=
  ObjectProperty.hom_ext _ (Thick.hom_ext fun b ↦ res_toSec R T.obj.B (homOfLE (Pair.le_fst hpq)).op b)

theorem aM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p :=
  ObjectProperty.hom_ext _ (Thick.hom_ext fun u ↦
    (congrArg (fun t ↦ t.hom u) ((pt T).appLE_map q.2 (homOfLE (Pair.le_fst hpq)).op)).trans
      (congrArg (fun t ↦ t.hom u) ((pt T).map_appLE p.2 (homOfLE (Pair.le_snd hpq)).op)).symm)

theorem hSec_res (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s))
    (hg : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a))
    (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q) :
    Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  set ρ := Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) with hρ
  let d : op q.1.2 ⟶ op p.1.2 := (homOfLE (Pair.le_snd hpq)).op
  have e1 : fv f (bM T p) = ρ (fv f (bM T q)) + fv f (resThk T hpq) := by
    rw [← bM_resThk T hpq]; exact f.2 _ _
  have e2 : ρ (fv f (aM T q)) + fv f (resThk T hpq) =
      secPullA T p (fv f ((affF s).map d)) + fv f (aM T p) := by
    have k := f.2 (aM T q) (resThk T hpq)
    rw [aM_resThk] at k
    exact k.symm.trans (f.2 ((affF s).map d) (aM T p))
  have e3 : g (op p.1.2) = Sec.res s (Pair.le_snd hpq) (g (op q.1.2)) +
      (show Sec s p.1.2.1 from fv f ((affF s).map d)) :=
    sub_eq_iff_eq_add'.1 (hg d)
  have e4 : ∀ u, secPullA T p (Sec.res s (Pair.le_snd hpq) u) = ρ (secPullA T q u) := fun u ↦
    (congrArg (fun m ↦ m.hom.φ u) (aM_resThk T hpq)).symm
  change ρ (secPullA T q (g (op q.1.2)) + fv f (aM T q) - fv f (bM T q)) =
    secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)
  rw [map_sub, map_add, e1, e3, map_add, e4]
  linear_combination e2

end GlobalTheory.CechDR.AffLoc
