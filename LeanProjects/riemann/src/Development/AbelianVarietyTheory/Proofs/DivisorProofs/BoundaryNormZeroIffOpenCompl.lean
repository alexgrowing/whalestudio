import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.Proof.boundary_norm_zero_iff_open_compl

theorem sec_self_eq_zero_iff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {m : ℕ} (L : LocPot X) (s : X → X → ℂ) (D : Fin m → Set X) (i : Fin m)
    (h : IsSNC A L s (Pi.single i 1) D) (y : X) : s y y = 0 ↔ y ∈ D i := by
  obtain ⟨ψ, -, hy, -, σ, -, hD, u, -, hu, hs⟩ := h y
  have hmem : y ∈ D i ↔ ∃ j, σ i = some j ∧ ψ y j = 0 := by
    have := Set.ext_iff.mp (hD i) y
    simpa [hy] using this
  rw [hs y hy, Finset.prod_eq_single i, hmem, mul_eq_zero]
  · simp only [hu y hy, false_or]
    cases σ i <;> simp
  · intro k _ hk
    cases σ k <;> simp [Pi.single_apply, hk]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem main {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) :
    IsBoundary A L s D → (∀ i y, normSec (L i) (s i) y = 0 ↔ y ∈ D i) ∧ IsOpen (⋃ i, D i)ᶜ := by
  intro hB
  refine ⟨fun i y => ?_, ?_⟩
  · rw [normSec, mul_eq_zero, or_iff_left (Real.exp_pos _).ne', norm_eq_zero]
    exact sec_self_eq_zero_iff A (L i) (s i) D i (hB i).2.2.1 y
  · rw [isOpen_compl_iff]
    refine isClosed_iUnion_of_finite fun i => ?_
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨ψ, -, hyψ, -, σ, -, hD, -⟩ := (hB i).2.2.1 y
    have hDi := hD i
    cases hσ : σ i with
    | none =>
      refine ⟨ψ.source, fun y' hy' hy'D => ?_, ψ.open_source, hyψ⟩
      have : y' ∈ D i ∩ ψ.source := ⟨hy'D, hy'⟩
      rw [hDi] at this
      obtain ⟨j, hj, -⟩ := this.2
      rw [hσ] at hj; cases hj
    | some j =>
      refine ⟨ψ.source ∩ ψ ⁻¹' {z | z j ≠ 0}, fun y' hy' hy'D => ?_,
        ψ.continuousOn.isOpen_inter_preimage ψ.open_source
          (isOpen_ne_fun (continuous_apply j) continuous_const), ⟨hyψ, ?_⟩⟩
      · have : y' ∈ D i ∩ ψ.source := ⟨hy'D, hy'.1⟩
        rw [hDi] at this
        obtain ⟨j', hj', h0⟩ := this.2
        rw [hσ] at hj'; cases hj'
        exact hy'.2 h0
      · intro h0
        apply hy
        have : y ∈ {y ∈ ψ.source | ∃ k, σ i = some k ∧ ψ y k = 0} := ⟨hyψ, j, hσ, h0⟩
        rw [← hDi] at this
        exact this.1

end GlobalTheory.Proof.boundary_norm_zero_iff_open_compl
