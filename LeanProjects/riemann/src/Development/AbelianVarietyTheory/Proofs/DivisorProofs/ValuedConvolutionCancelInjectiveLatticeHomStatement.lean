import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuedConvolution_cancel_injective_latticeHom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  first | exact @GlobalTheory.UT.sumV_cancel_hom | exact GlobalTheory.UT.sumV_cancel_hom | (intros; apply GlobalTheory.UT.sumV_cancel_hom <;> assumption)
