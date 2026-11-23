import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCohomologyProjectiveModule
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_cohomology_projective_module : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k], (∀ (B₀ : Over (Sp (AlgebraicClosure k))) [GrpObj B₀] [IsCommMonObj B₀], IsAbelianScheme B₀ → ∀ b : OAct (𝓞 F) B₀, letI := tensorModule (dp0 (AlgebraicClosure k)) (𝟙 _) b; Module.Projective (AlgebraicClosure k ⊗[ℤ] 𝓞 F) (HdR B₀)) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  first | exact @GlobalTheory.HdRDescent.projective_of_algebraicClosure | exact GlobalTheory.HdRDescent.projective_of_algebraicClosure | (intros; apply GlobalTheory.HdRDescent.projective_of_algebraicClosure <;> assumption)
