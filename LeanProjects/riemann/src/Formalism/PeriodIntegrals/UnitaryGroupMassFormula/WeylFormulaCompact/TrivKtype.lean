import Formalism.PeriodIntegrals.WeylForK

open PI PI.UpqRep Matrix

noncomputable section

namespace PI.WeylForKInhab

def triv (N : ℕ) : Matrix (Fin N) (Fin N) ℂ → (ℂ →L[ℂ] ℂ) := fun _ => 1

theorem diag_mem {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    first
      | simp [← Complex.exp_conj, ← Complex.exp_add]
      | (rw [Pi.star_apply, ← Complex.exp_conj, ← Complex.exp_add]
         simp [Complex.conj_ofReal])
      | (rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]
         simp)
  · simp only [Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem triv_urep {N : ℕ} (ε : Fin N → Bool) : IsURepOn (Kset ε) (triv N) := by
  refine ⟨⟨rfl, fun a _ b _ => rfl⟩, fun g _ v => rfl, fun v => ?_⟩
  show ContinuousOn (fun _ => (1 : ℂ →L[ℂ] ℂ) v) _
  exact continuousOn_const

theorem triv_ktype {N : ℕ} (ε : Fin N → Bool) : IsKTypeOf ε (triv N) 0 ⊤ := by
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, fun S' _ _ => Ideal.eq_bot_or_top S',
    ⟨1, Submodule.mem_top, one_ne_zero, fun θ _ => by simp [triv]⟩, ?_⟩
  intro μ v _ hv hw
  have hμ : μ = 0 := by
    funext b
    by_contra hb
    have hb' : μ b ≠ 0 := hb
    have h := hw (Pi.single b (Real.pi / μ b)) (diag_mem ε _)
    have hs : (∑ a, μ a * (Pi.single b (Real.pi / μ b) : Fin N → ℝ) a) = Real.pi := by
      rw [Finset.sum_eq_single b]
      · rw [Pi.single_eq_same]
        field_simp
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ b) h'
    rw [hs] at h
    have h' : v = 0 := by
      first
        | simpa [triv, Complex.exp_pi_mul_I] using h
        | (simp [triv, Complex.exp_pi_mul_I] at h
           linear_combination h / 2)
    exact hv h'
  subst hμ
  exact ⟨0, fun a b h => absurd rfl h, by simp⟩

end PI.WeylForKInhab
