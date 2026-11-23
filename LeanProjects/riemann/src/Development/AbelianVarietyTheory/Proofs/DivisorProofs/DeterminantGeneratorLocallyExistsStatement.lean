import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorLocallyExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_locally_exists : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M), ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  first | exact @GlobalTheory.RealMult.LocalGen.exists_affine_detGen | exact GlobalTheory.RealMult.LocalGen.exists_affine_detGen | (intros; apply GlobalTheory.RealMult.LocalGen.exists_affine_detGen <;> assumption)
