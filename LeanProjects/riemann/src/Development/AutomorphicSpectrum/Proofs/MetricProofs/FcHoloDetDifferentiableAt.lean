import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcHolo_det_differentiableAt {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype n] [DecidableEq n] (M : E → Matrix n n ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) x) :
    DifferentiableAt ℂ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ s : Finset n, DifferentiableAt ℂ (fun b => ∏ i ∈ s, M b (σ i) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).fun_mul ih
  exact key _

theorem fcHolo : ∀ (m p q : ℕ) (B : Set (Fin m → ℂ)), IsOpen B → ∀ (A : (Fin m → ℂ) → Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : (Fin m → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), (∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) → (∀ i j, DifferentiableOn ℂ (fun b => Φ b i j) B) → (∀ b ∈ B, A b * Φ b = 0 ∧ (A b).rank = p ∧ (Φ b).rank = q) → DifferentiableOn ℂ (fun b => (fromRows (Φ b)ᴴ (A b)).det / ((Φ b)ᴴ * Φ b).det) B := by
  intro m p q B hB A Φ hA hΦ hex b₀ hb₀
  have hn : B ∈ nhds b₀ := hB.mem_nhds hb₀
  have hnum : DifferentiableAt ℂ (fun b => (fromRows (Φ b₀)ᴴ (A b)).det) b₀ := by
    apply fcHolo_det_differentiableAt
    intro i j
    rcases i with i | i
    · simp
    · simpa using (hA i j).differentiableAt hn
  have hden : DifferentiableAt ℂ (fun b => ((Φ b₀)ᴴ * Φ b).det) b₀ := by
    apply fcHolo_det_differentiableAt
    intro i j
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => ((hΦ k j).differentiableAt hn).const_mul _
  obtain ⟨e1, e2, e3⟩ := hex b₀ hb₀
  have h0 : ((Φ b₀)ᴴ * Φ b₀).det ≠ 0 := (fcIndep p q _ _ e1 e2 e3).1
  have hq : DifferentiableAt ℂ
      (fun b => (fromRows (Φ b₀)ᴴ (A b)).det / ((Φ b₀)ᴴ * Φ b).det) b₀ := by
    simp only [div_eq_mul_inv]
    exact hnum.fun_mul (hden.fun_inv h0)
  refine (hq.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hn, hden.continuousAt.eventually_ne h0] with b hb hne
  obtain ⟨f1, f2, f3⟩ := hex b hb
  obtain ⟨g1, -, g3⟩ := fcIndep p q _ _ f1 f2 f3
  rw [div_eq_div_iff g1 hne]
  exact (g3 _).symm

end GlobalTheory.CompanionTheory.Ar.Flat
