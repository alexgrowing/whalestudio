import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturality
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality : ∀ (p : ℕ) (R R' : Type) [CommRing R] [CommRing R'] (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A') (σ : R →+* R') (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t' (m.pull c) ((t'.semiHom t m).rig x) := by
  first | exact @GlobalTheory.PtExtNat.isCan_pull | exact GlobalTheory.PtExtNat.isCan_pull | (intros; apply GlobalTheory.PtExtNat.isCan_pull <;> assumption)
