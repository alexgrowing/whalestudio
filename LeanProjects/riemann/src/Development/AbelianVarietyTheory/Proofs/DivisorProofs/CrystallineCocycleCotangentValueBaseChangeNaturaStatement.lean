import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNatura
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCocycleCotangentValue_baseChange_natural : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ) (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D') (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), (∀ r, a.φ r = s r) → cotVal (m.coef.pullbackOneCocycle f) y' = s.cot (cotVal f y) + dUnit R' (show D' from ev f a) := by
  first | exact @GlobalTheory.PtExt.cotVal_pull | exact GlobalTheory.PtExt.cotVal_pull | (intros; apply GlobalTheory.PtExt.cotVal_pull <;> assumption)
