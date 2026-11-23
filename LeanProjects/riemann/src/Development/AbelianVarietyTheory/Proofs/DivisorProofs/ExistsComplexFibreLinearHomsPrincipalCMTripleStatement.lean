import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTriple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.GramBaseChange.exists_complex_fibre | exact GlobalTheory.GramBaseChange.exists_complex_fibre | (intros; apply GlobalTheory.GramBaseChange.exists_complex_fibre <;> assumption)
