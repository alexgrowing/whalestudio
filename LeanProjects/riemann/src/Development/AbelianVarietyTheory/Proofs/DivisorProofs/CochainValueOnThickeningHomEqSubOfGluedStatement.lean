import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainValueOnThickeningHomEqSubOfGlued
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B), (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) → (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) → fv f φ = G' - φ.hom.φ G := by
  first | exact @GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | exact GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | (intros; apply GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued <;> assumption)
