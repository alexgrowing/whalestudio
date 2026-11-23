import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaHalf

theorem exists_real_of_half {g : ℕ} {c : Fin g → ℂ} (hc : ∀ i, c i = 0 ∨ c i = 1 / 2) :
    ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := by
  refine ⟨fun i => if c i = 0 then 0 else 1 / 2, funext fun i => ?_⟩
  rcases hc i with h | h
  · show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_pos h, h, Complex.ofReal_zero]
  · have h0 : c i ≠ 0 := by rw [h]; norm_num
    show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_neg h0, h]
    norm_num

theorem thetaChar_holomorphic_ne_zero : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  intro g c₁ c₂ h₁ h₂
  obtain ⟨a, rfl⟩ := exists_real_of_half h₁
  obtain ⟨b, rfl⟩ := exists_real_of_half h₂
  refine ⟨fun τ hs hp => ⟨GlobalTheory.CanTh.differentiable_thetaChar (GlobalTheory.CanTh.mem_thetaDomain hp) a b, ?_⟩, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact GlobalTheory.CanTh.thetaChar_ne_zero hs hp a b (funext hcon)
  · intro m B h τ _ hτ hdiff
    have hT : ∀ i j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => τ w.1 i j) (B ×ˢ Set.univ) :=
      fun i j => (hdiff i j).2.comp differentiableOn_fst fun w hw => hw.1
    have hZ : DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 *ᵥ w.2) (B ×ˢ Set.univ) := by
      rw [differentiableOn_pi]
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have hj : ∀ j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 i j) (B ×ˢ Set.univ) :=
        fun j => (hdiff i j).1.comp differentiableOn_fst fun w hw => hw.1
      refine DifferentiableOn.fun_sum fun j _ => (hj j).mul ?_
      have hs : Differentiable ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.2 j) := by fun_prop
      exact hs.differentiableOn
    have hdom : ∀ w ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)), τ w.1 ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) :=
      fun w hw => GlobalTheory.CanTh.mem_thetaDomain (hτ w.1 hw.1).2
    exact GlobalTheory.CanTh.differentiableOn_thetaChar hT hZ hdom a b

end GlobalTheory.ThetaHalf
