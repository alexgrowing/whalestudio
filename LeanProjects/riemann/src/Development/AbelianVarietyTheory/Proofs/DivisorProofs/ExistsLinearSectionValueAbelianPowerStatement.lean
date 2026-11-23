import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_sectionValue_abelianPower : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  first | exact @GlobalTheory.SecValLin.exists_linear_valR_sec | exact GlobalTheory.SecValLin.exists_linear_valR_sec | (intros; apply GlobalTheory.SecValLin.exists_linear_valR_sec <;> assumption)
