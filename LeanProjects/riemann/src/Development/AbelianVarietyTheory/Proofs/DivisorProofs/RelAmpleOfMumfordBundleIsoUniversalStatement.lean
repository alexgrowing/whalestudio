import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  first | exact @GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | exact GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | (intros; apply GlobalTheory.MumAmple.relAmple_of_lam_iso_univ <;> assumption)
