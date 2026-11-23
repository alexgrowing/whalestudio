import Formalism.PeriodIntegrals.FdegScale

noncomputable section

namespace PI.UnitaryGroupMassFormula.FdegScale

open PI PI.UpqRep MeasureTheory Finset
open scoped InnerProductSpace

lemma fdegHC_pos {n : ℕ} {lam : Fin n → ℝ} (h : IsHCParam lam) : 0 < fdegHC lam := by
  unfold fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (h.1.injective.ne (ne_of_lt hab)))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have h' : (a : ℕ) < (b : ℕ) := hab
    rw [sub_pos]
    exact_mod_cast h'

lemma fdeg_smul_eq {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Nontrivial V] (μ : Measure (UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : NNReal)
    (hs : 0 < s) (d₁ d : ℝ) (h₁ : IsFdeg μ σ d₁) (h₂ : IsFdeg ((s : ENNReal) • μ) σ d) :
    d = d₁ / (s : ℝ) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have e₁ := (h₁.2 x x x x).2
  have e₂ := (h₂.2 x x x x).2
  rw [integral_smul_measure, e₁, ENNReal.coe_toReal, Complex.real_smul] at e₂
  have hA : (⟪x, x⟫_ℂ) ≠ 0 := inner_self_ne_zero.mpr hx
  have hd₁ : (d₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.1.ne'
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast h₂.1.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
  have key : (d : ℂ) * ((s : ℝ) : ℂ) = d₁ := by
    field_simp at e₂
    linear_combination e₂
  have key' : d * (s : ℝ) = d₁ := by exact_mod_cast key
  field_simp
  exact key'

theorem fdegScale_of (h : PI.HCFdeg) : PI.FdegScale := by
  intro n ε s hs lam hlam
  obtain ⟨c, hc, hC⟩ := h n ε
  refine ⟨c * fdegHC lam / (s : ℝ), div_pos (mul_pos hc (fdegHC_pos hlam)) (by exact_mod_cast hs), ?_⟩
  intro V _ _ σ d hDS hF
  have : CompleteSpace V := hDS.1
  have : Nontrivial V := hDS.2.1
  exact fdeg_smul_eq (muG ε) σ s hs _ d (hC lam V σ hlam hDS) hF

end PI.UnitaryGroupMassFormula.FdegScale
