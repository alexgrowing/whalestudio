import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross

open PositivityTheory.RgEis in

theorem stage_eis : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  intro hSt G _ W _ _ _ Γ K Q P c ρ ξ lam Λ s w Ms hPQ hξ hΛ hsec hMs hconv hre g
  set f : G → W := fun x => Complex.exp (Λ x + s * ξ x) • sec K P c ρ x w with hf
  have hfinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro γ hγ hP x
    simp only [hf]
    rw [hΛ γ hγ hP x, hξ γ hγ (hPQ hP) x, hsec γ hγ hP x]
  have hnorm : ∀ x, ‖f x‖ ≤ Ms * Real.exp (lam x) := by
    intro x
    simp only [hf]
    rw [norm_smul, Complex.norm_exp, hre x, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right (hMs x) (Real.exp_pos _).le
  have hsum : Summable fun q : Cos P Γ => ‖f (rep q * g)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hnorm _) ((hconv g).mul_left Ms)
  obtain ⟨-, -, hstage⟩ := hSt G W P (Γ ⊓ Q) Γ f inf_le_left (fun γ hγ hP => ⟨hγ, hPQ hP⟩) hfinv g hsum
  have hR : eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w = ∑' q : Cos P Γ, f (rep q * g) := rfl
  rw [hR, hstage]
  unfold eis
  refine tsum_congr fun r => ?_
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  simp only [hf]
  rw [hξ _ (Subgroup.mem_inf.mp hq).1 (Subgroup.mem_inf.mp hq).2, Complex.exp_add, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisCross
