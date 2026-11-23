import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.LieStable

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem hasDerivAt_conj_curve (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (X * Y - Y * X) 0 := by
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
  have h : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)))
      (NormedSpace.exp ((0 : ℝ) • X) * X * Y * NormedSpace.exp ((0 : ℝ) • (-X)) +
        NormedSpace.exp ((0 : ℝ) • X) * Y * (NormedSpace.exp ((0 : ℝ) • (-X)) * -X)) 0 :=
    (h₁.mul_const Y).fun_mul h₂
  refine h.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg, sub_eq_add_neg]

theorem conj_mem {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : GlobalTheory.LinRed.IsLinRed G)
    {𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {g Y : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (hY : Y ∈ 𝔤) : g * Y * g⁻¹ ∈ 𝔤 := by
  obtain ⟨-, hmul, hunit, hinv, -, -, -⟩ := hG
  rw [h𝔤] at hY ⊢
  intro t
  have hconj : t • (g * Y * g⁻¹) = g * (t • Y) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, Matrix.exp_conj g (t • Y) (hunit g hg)]
  exact hmul _ (hmul _ hg _ (hY t)) _ (hinv g hg)

theorem lieAlg_stable : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ 𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G) →
      (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) ∧ ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤 := by
  intro n G hG 𝔤 h𝔤
  have hexp : ∀ X ∈ 𝔤, ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := fun X hX => (h𝔤 X).1 hX
  refine ⟨fun X hX => ?_, fun X hX Y hY => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hstar⟩ := hG
    refine (h𝔤 _).2 fun t => ?_
    have ht : t • Xᴴ = (t • X)ᴴ := by
      rw [Matrix.conjTranspose_smul, star_trivial]
    rw [ht, Matrix.exp_conjTranspose]
    exact hstar _ (hexp X hX t)
  · have hmem : ∀ s : ℝ,
        NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • (-X)) ∈ 𝔤 := by
      intro s
      rw [smul_neg, Matrix.exp_neg]
      exact GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 (hexp X hX s) hY
    have hd := hasDerivAt_iff_tendsto_slope.1 (GlobalTheory.CompanionTheory.LieStable.hasDerivAt_conj_curve X Y)
    refine (Submodule.closed_of_finiteDimensional 𝔤).mem_of_tendsto hd
      (Filter.Eventually.of_forall fun s => ?_)
    rw [slope_def_module]
    exact 𝔤.smul_mem _ (𝔤.sub_mem (hmem s) (hmem 0))

end GlobalTheory.CompanionTheory.LieStable

end
