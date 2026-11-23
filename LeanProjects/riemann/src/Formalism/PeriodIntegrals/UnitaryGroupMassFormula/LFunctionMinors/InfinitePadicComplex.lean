import Mathlib
import Formalism.PeriodIntegrals.WwMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice

open MvPolynomial Finset

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

instance infinitePadicComplex (l : ℕ) [Fact l.Prime] : Infinite ℂ_[l] :=
  Infinite.of_injective (Nat.cast : ℕ → ℂ_[l]) Nat.cast_injective

theorem Lfun_sum (hLin : LLin) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    Lfun l N0 N1 Th (∑ i ∈ s, f i) = ∑ i ∈ s, Lfun l N0 N1 Th (f i) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := hLin Lt l N0 N1 Th
  refine Finset.induction_on s ?_ ?_
  · simp [hzero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

theorem applyQ_eq {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l])
    (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    applyQ l N0 N1 Th Q y' = Lfun l N0 N1 Th (aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q) := by
  unfold applyQ Lfun wt
  exact Finset.sum_congr rfl fun α _ => by ring

theorem wwMain_of (hE : EvalH) (hL : LH) (hLin : LLin) (hD : DeXCB) : WwMain := by
  intro Lt _ _ l _ N0 N1 nu Th ph Q hQ y'
  rw [applyQ_eq l N0 N1 Th Q y']
  have heval : ∀ (g : Lt × Fin N0 × ℕ → MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l])
      (z : Lt × Fin N0 × Fin N1 → ℂ_[l]), eval z (aeval g Q) = eval (fun v => eval z (g v)) Q := by
    intro g z
    have h : (aeval z).comp (aeval g) = aeval (R := ℂ_[l]) (fun v => aeval z (g v)) :=
      MvPolynomial.algHom_ext fun v => by simp
    have h2 := congrArg (fun φ : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l] →ₐ[ℂ_[l]] ℂ_[l] => φ Q) h
    simpa [MvPolynomial.coe_aeval_eq_eval] using h2
  have hP : aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q =
      ∑ I : ColChoice N1 nu, C (minY N1 nu I y') * Hpol l N0 N1 ph (Gxz N0 N1 nu I) := by
    apply MvPolynomial.funext
    intro z
    rw [heval]
    have hy : (fun v : Lt × Fin N0 × ℕ => eval z (∑ b : Fin N1,
        C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1))) =
        fun v => (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j) v.1 v.2.1 v.2.2 := by
      funext v
      simp [mul_comm]
    rw [hy, hQ (fun s a j => ∑ b : Fin N1, z (s, a, b) * y' s b j), hD Lt l N0 N1 nu z y']
    simp only [map_sum, map_mul, eval_C, C_mul', map_smul, smul_eq_mul, MvPolynomial.smul_eval,
      hE Lt l N0 N1 ph]
  rw [hP, Lfun_sum hLin, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hLin Lt l N0 N1 Th).2.2, hL Lt l N0 N1 Th ph]

end PI.WwMainW
