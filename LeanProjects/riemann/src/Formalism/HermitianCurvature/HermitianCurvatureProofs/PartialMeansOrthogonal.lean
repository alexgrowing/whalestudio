import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A6

namespace Formalism.FourierDecayAlt.P

namespace A6x1

theorem norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ

end A6x1

theorem doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by
  intro E _ _ A B _ _ u e₁ e₂
  rw [Fintype.sum_prod_type, mul_inv, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, Finset.smul_sum (r := e₁ ρ)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]

theorem partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by
  intro E _ _ A B _ _ u e₂ h ρ ρ' hne
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp [h ρ ρ' _ _ hne]

theorem orthogonalMeanNorm : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]

theorem averageBoundOfSteps : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := by
  intro hM hP hO E _ _ A B _ _ u T e₁ e₂ hT he h
  rw [hM E A B u e₁ e₂]
  have h1 := hO E A (fun ρ => (Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)) e₁ he
    (hP E A B u e₂ h)
  have h2 := hT ((Fintype.card A : ℂ)⁻¹ •
    ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)))
  calc _ ≤ ‖(Fintype.card A : ℂ)⁻¹ •
        ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))‖ ^ 2 := by
        gcongr
    _ = _ := by rw [h1]; ring

theorem averageBound : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm

end Formalism.FourierDecayAlt.P
