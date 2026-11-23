import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.heisenbergEigen_proportional : ∀ {k : Type} [Field k] {κ : Type} [Fintype κ] (ψk : AddChar k ℂ) (Λ : AddSubgroup ((κ → k) × (κ → k)))
    (χ : (κ → k) × (κ → k) → ℂ) (f g : (κ → k) → ℂ),
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ) →
    (∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * g (ξ + l.1) = χ l * g ξ) → f ≠ 0 →
    (∀ η : κ → k, (∀ b : κ → k, ((0 : κ → k), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ) →
    ∃ c : ℂ, g = c • f := by
  intro k _ κ _ ψk Λ χ f g hf hg hf0 hann
  have hψ : ∀ x : k, ψk x ≠ 0 := by
    intro x hx
    have h2 : ψk (x + -x) = ψk x * ψk (-x) := AddChar.map_add_eq_mul ψk x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
    exact one_ne_zero h2
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, f ξ₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (funext hc)
  refine ⟨g ξ₀ / f ξ₀, ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : (κ → k) → ℂ, ∀ ξ, h ξ = g ξ - g ξ₀ / f ξ₀ * f ξ :=
    ⟨_, fun _ => rfl⟩
  have hid : ∀ l ∈ Λ, ∀ ξ, ψk (ξ ⬝ᵥ l.2 + (2 : k)⁻¹ * (l.1 ⬝ᵥ l.2)) * h (ξ + l.1) = χ l * h ξ := by
    intro l hl ξ
    have e1 := hf l hl ξ
    have e2 := hg l hl ξ
    rw [hh, hh]
    linear_combination e2 - (g ξ₀ / f ξ₀) * e1
  have h0 : h ξ₀ = 0 := by rw [hh, div_mul_cancel₀ _ hξ₀, sub_self]
  have hzero : ∀ ξ, h ξ = 0 := by
    intro ξ
    by_contra hne
    have key : ∀ b, ((0 : κ → k), b) ∈ Λ → ψk ((ξ - ξ₀) ⬝ᵥ b) = 1 := by
      intro b hb
      have e1 := hid _ hb ξ
      have e2 := hf _ hb ξ₀
      simp only [zero_dotProduct, mul_zero, add_zero] at e1 e2
      have a1 : ψk (ξ ⬝ᵥ b) = χ (0, b) := mul_right_cancel₀ hne e1
      have a2 : ψk (ξ₀ ⬝ᵥ b) = χ (0, b) := mul_right_cancel₀ hξ₀ e2
      have hχ : χ (0, b) ≠ 0 := a2 ▸ hψ _
      have hs : ψk ((ξ - ξ₀) ⬝ᵥ b) * ψk (ξ₀ ⬝ᵥ b) = ψk (ξ ⬝ᵥ b) := by
        rw [← AddChar.map_add_eq_mul, sub_dotProduct, sub_add_cancel]
      rw [a1, a2] at hs
      exact mul_right_cancel₀ hχ (hs.trans (one_mul _).symm)
    obtain ⟨y, hy⟩ := hann _ key
    have e := hid _ hy ξ₀
    have hx : ξ₀ + (ξ - ξ₀) = ξ := by abel
    simp only [h0, mul_zero, hx] at e
    exact hne ((mul_eq_zero.mp e).resolve_left (hψ _))
  funext ξ
  have := hzero ξ
  rw [hh, sub_eq_zero] at this
  rw [Pi.smul_apply, smul_eq_mul, this]
