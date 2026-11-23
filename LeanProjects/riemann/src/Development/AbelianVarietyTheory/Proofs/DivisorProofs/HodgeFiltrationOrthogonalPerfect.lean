import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCrystalPairingSwapEqNegFlipStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PoincareKer.mem_fil_left : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left,
    AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ x : HdR A, (∀ y ∈ Fil B, φ x y = 0) → x ∈ Fil A := by
  intro hHdR R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ x hx
  have hφ' := GlobalTheory.T.poincareCrystalPairing_swap_eq_neg_flip R A B P hP.isLB φ hφ
  refine GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing hHdR R B A g hB hA hgB hgA (AbDual.swap P) hP.swap (-φ.flip) hφ' x ?_
  intro y hy
  simp [hx y hy]
