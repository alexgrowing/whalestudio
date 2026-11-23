import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SplitWeil.FourierSurj

theorem hat_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have key := FourierPi.fourier_pi k n ψ hc h1 ν hν
  have hhat : ∀ f : (n → k) → ℂ,
      hat ψ ν f = fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro f
    funext y
    simp only [hat, dotProduct_comm y]
  have hmem : ∀ f ∈ SB (n → k), hat ψ ν f ∈ SB (n → k) := fun f hf => hhat f ▸ (key f hf).1
  refine ⟨fun Φ₀ => hmem _ Φ₀.2, fun g => ?_⟩
  have hcomp : ∀ (e : (n → k) ≃ₜ (n → k)), ∀ f ∈ SB (n → k), (fun x => f (e x)) ∈ SB (n → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hg' : (fun x => g.1 (-x)) ∈ SB (n → k) := hcomp (Homeomorph.neg _) _ g.2
  refine ⟨⟨_, hmem _ hg'⟩, ?_⟩
  funext u
  have hf : (fun x => g.1 (-(x + -u))) ∈ SB (n → k) := hcomp (Homeomorph.addRight (-u)) _ hg'
  have h2 := (key _ hf).2
  simp only [zero_add, neg_neg] at h2
  rw [← h2]
  show ∫ β, hat ψ ν (fun x => g.1 (-x)) β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν) = _
  congr 1
  funext y
  rw [hhat, ← integral_mul_const,
    ← integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) _ (-u)]
  congr 1
  funext x
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_dotProduct, neg_add_cancel_right]

end GlobalTheory.SplitWeil.FourierSurj
