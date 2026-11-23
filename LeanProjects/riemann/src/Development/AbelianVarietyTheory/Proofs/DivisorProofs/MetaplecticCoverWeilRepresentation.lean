import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqGaussianOfFderivEqMulVecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqMulVecOfSchrodingerAnnihilatedStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.metaplectic_euclidean_gaussian : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (Continuous fun x : G × Sch l => omS x.1 x.2) ∧ ∀ (g : G) (P Q : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) → ∃ c : ℂ, c ^ 2 * P.det = 1 ∧ ∀ x : EuclideanSpace ℝ l, omS g φ x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _
  obtain ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.metaplecticGaussianNormalisedAlt l
  refine ⟨G, iG, tG, hG, pr, om, omS, φ, h1, h2, h3, h4, h5, h6, h7,
    GlobalTheory.T.continuous_metaplectic_schwartz_action_prod l G pr om omS h1.continuous h4 h5 h6, ?_⟩
  intro g P Q hP hQ
  refine ⟨omS g φ 0, h9 g P hP, ?_⟩
  obtain ⟨hdet, hS⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm l (pr g).1 P Q hP hQ (pr g).2
  have hann : ∀ j : l, dRho ((pr g).1 *ᵥ Pi.single (.inl j) 1) (omS g φ) =
      I • dRho ((pr g).1 *ᵥ Pi.single (.inr j) 1) (omS g φ) := fun j => by
    rw [← omS_dRho h5 h6, ← omS_dRho h5 h6, h8 j, map_smul]
  have hd := GlobalTheory.T.fderiv_eq_mulVec_of_schrodinger_annihilated l (pr g).1 P Q hP hQ hdet (omS g φ) hann
  rw [hS.eq] at hd
  exact GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm l (-(Q * P⁻¹)) (omS g φ) hS hd
