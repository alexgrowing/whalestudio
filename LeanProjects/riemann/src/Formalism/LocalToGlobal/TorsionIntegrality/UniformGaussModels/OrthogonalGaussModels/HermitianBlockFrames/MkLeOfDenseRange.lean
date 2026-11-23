import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK

noncomputable section
open Cardinal

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

theorem tendsto_of_choice {X Y : Type} [MetricSpace X] (f : Y → X) (x : X) (u : ℕ → Y)
    (hu : ∀ k : ℕ, dist x (f (u k)) < 1 / ((k : ℝ) + 1)) :
    Filter.Tendsto (fun k => f (u k)) Filter.atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_comm]
  have hk' : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hk 1
  calc dist x (f (u k)) < 1 / ((k : ℝ) + 1) := hu k
    _ ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hk'
    _ < ε := hN

theorem mk_le_of_denseRange {X Y : Type} [MetricSpace X] {f : Y → X} (hf : DenseRange f) :
    #X ≤ #(ℕ → Y) := by
  have h : ∀ x : X, ∀ k : ℕ, ∃ y, dist x (f y) < 1 / ((k : ℝ) + 1) := fun x k =>
    Metric.denseRange_iff.mp hf x _ (by positivity)
  choose u hu using h
  refine Cardinal.mk_le_of_injective (f := u) ?_
  intro x x' hxx'
  have hx := tendsto_of_choice f x (u x) (hu x)
  have hx' := tendsto_of_choice f x' (u x') (hu x')
  rw [hxx'] at hx
  exact tendsto_nhds_unique hx hx'

theorem mk_padic_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_denseRange (Padic.denseRange_ratCast p)
    _ = 𝔠 := by rw [← power_def, Cardinal.mkRat, Cardinal.mk_nat, aleph0_power_aleph0]

theorem mk_padicAlgCl_le (p : ℕ) [Fact p.Prime] : #(PadicAlgCl p) ≤ 𝔠 :=
  (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
    (max_le (mk_padic_le p) aleph0_le_continuum)

theorem mk_padicComplex_le (p : ℕ) [Fact p.Prime] : #ℂ_[p] ≤ 𝔠 := by
  calc #ℂ_[p] ≤ #(ℕ → PadicAlgCl p) := mk_le_of_denseRange UniformSpace.Completion.denseRange_coe
    _ = #(PadicAlgCl p) ^ ℵ₀ := by rw [← power_def, Cardinal.mk_nat]
    _ ≤ 𝔠 ^ ℵ₀ := power_le_power_right (mk_padicAlgCl_le p)
    _ = 𝔠 := continuum_power_aleph0

theorem mk_padicComplex (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 :=
  le_antisymm (mk_padicComplex_le p) (continuum_le_cardinal_of_nontriviallyNormedField _)

theorem exists_iota (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
  · rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  · exact Cardinal.eq.mp (by rw [Cardinal.mk_complex, mk_padicComplex])

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
