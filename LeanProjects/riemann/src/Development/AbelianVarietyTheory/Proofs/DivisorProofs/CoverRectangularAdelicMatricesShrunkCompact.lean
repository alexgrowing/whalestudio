import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem cover_rect_adMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  intro F E _ _ _ _ _ σ hσ j m
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.GodementSectionReduction.cover_adele F E σ hσ
  choose Y hY h using h
  refine ⟨Ω, (C ^ m) ^ j, hΩ, fun μ =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i)).card = ∏ i, (Y (μ i)).card ^ m := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (μ i)) m).trans (le_of_eq ?_)
    simp only [bse, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul _ (μ _), mul_comm m]
  · choose x₀ y hy ω hω e using fun i k => h (μ i) (x i k)
    refine ⟨Matrix.of x₀, Matrix.of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), Matrix.of ω,
      fun i k => hω i k, ?_⟩
    ext i k
    rw [Matrix.add_apply, Matrix.add_apply, ← add_assoc]
    simp only [tor, GlobalTheory.Eis.Conv.dg, Matrix.diagonal_mul, adMat, Matrix.map_apply, Matrix.of_apply, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact e i k

end GlobalTheory.SphEis

end
