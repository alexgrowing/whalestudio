import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseCochainCoboundaryEqChernCocycleAl
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseCochain_coboundary_eq_chernCocycle' : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (L : LB X.left) (w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))), IsChern (dp0 R) _ L (CatCoh.H2.mk _ w) → ∃ n : Fn1 X, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt X E), Sm L.U z → ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) = w.1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) := by
  first | exact @GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle | exact GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle | (intros; apply GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle <;> assumption)
