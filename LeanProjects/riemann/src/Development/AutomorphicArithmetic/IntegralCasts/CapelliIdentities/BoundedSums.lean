import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

noncomputable def UpperTheory.Reformulated.B.BoundedSums.Bdd :
    {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop :=
    fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), V.Ge K (s n)

noncomputable def UpperTheory.Reformulated.B.BoundedSums.BddS :
    {C : Type} → [inst : Field C] → {σ : Type} → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → MvPowerSeries σ C) → Prop :=
    fun {C : Type} [Field C] {σ : Type} (V : Formalism.L2.FormalSeriesBounds.VF C) (f : ℕ → MvPowerSeries σ C) ↦
      ∀ (μ : σ →₀ ℕ), UpperTheory.Reformulated.B.BoundedSums.Bdd V fun (n : ℕ) ↦ (MvPowerSeries.coeff μ : MvPowerSeries σ C → C) (f n)

private theorem UpperTheory.Reformulated.B.BoundedSums.bdd_sum {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {α : Type}
    (T : Finset α) (s : α → ℕ → C) (h : ∀ a ∈ T, UpperTheory.Reformulated.B.BoundedSums.Bdd V (s a)) :
    UpperTheory.Reformulated.B.BoundedSums.Bdd V fun n ↦ ∑ a ∈ T, s a n := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simpa using Formalism.L2.FormalSeriesBounds.VF.Ge.zero (V := V) 0⟩
  | insert a T ha ih =>
    obtain ⟨K, hK⟩ := h a (Finset.mem_insert_self a T)
    obtain ⟨L, hL⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨min K L, fun n => ?_⟩
    show V.Ge (min K L) (∑ b ∈ insert a T, s b n)
    rw [Finset.sum_insert ha]
    exact ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))

private theorem UpperTheory.Reformulated.B.BoundedSums.bddS_mul {C : Type} [Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ : Type}
    {f g : ℕ → MvPowerSeries σ C} (hf : UpperTheory.Reformulated.B.BoundedSums.BddS V f)
    (hg : UpperTheory.Reformulated.B.BoundedSums.BddS V g) : UpperTheory.Reformulated.B.BoundedSums.BddS V fun n ↦ f n * g n := by
  classical
  intro μ
  have h := UpperTheory.Reformulated.B.BoundedSums.bdd_sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (fun p n => MvPowerSeries.coeff p.1 (f n) * MvPowerSeries.coeff p.2 (g n)) (fun p _ => by
      obtain ⟨K, hK⟩ := hf p.1
      obtain ⟨L, hL⟩ := hg p.2
      exact ⟨K + L, fun n => (hK n).mul (hL n)⟩)
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n => ?_⟩
  show V.Ge K (MvPowerSeries.coeff μ (f n * g n))
  rw [MvPowerSeries.coeff_mul]
  exact hK n

theorem UpperTheory.Reformulated.B.BoundedSums.prod :
    ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C},
      (∀ i ∈ S, UpperTheory.Reformulated.B.BoundedSums.BddS V (f i)) → UpperTheory.Reformulated.B.BoundedSums.BddS V fun (n : ℕ) ↦ ∏ i ∈ S, f i n := by
  intro C _ V σ ι S f h
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ
    refine ⟨0, fun n => ?_⟩
    show V.Ge 0 (MvPowerSeries.coeff μ (∏ i ∈ (∅ : Finset ι), f i n))
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    split_ifs
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | insert a S ha ih =>
    have h2 := UpperTheory.Reformulated.B.BoundedSums.bddS_mul (h a (Finset.mem_insert_self a S))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.prod_insert ha] using h2
