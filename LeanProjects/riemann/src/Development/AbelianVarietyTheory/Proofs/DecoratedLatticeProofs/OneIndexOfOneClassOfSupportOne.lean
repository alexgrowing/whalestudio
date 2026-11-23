import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain

theorem exists_affPt_of_flat_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) (h0 : flat ψ ν μ Φ 1 h ≠ 0) :
    ∃ x₀ e, Φ ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply h0
  funext x₀
  have key : ∀ e, om μ 1 h Φ (affPt 1 x₀ e) = 0 := fun e => by
    have h1 : Φ ((h⁻¹).val * affPt 1 x₀ e * (1 : GL (n' ⊕ Fin (c + 1)) k).val) = 0 := by
      rw [Units.val_one, Matrix.mul_one]; exact hne x₀ e
    exact mul_eq_zero_of_right _ h1
  unfold flat opE
  simp only [key, zero_mul, integral_zero, Pi.zero_apply]

theorem oneIndex_of_oneClass_of_supportOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
      [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t]
      [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c hjc β hβ
  have := hν.1
  obtain ⟨h, rfl, h0⟩ := hβ
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c hjc h h0
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (ψ := S.ψ) (ν := ν) (h₂' := 1) (h₂ := u) (by omega)
    (HL.1 j (c + 1) (by omega)) rfl
    ((DoubleCoset.eq _ _ _ _).2 ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩)).1 h0
  obtain ⟨x₀, e, he⟩ := exists_affPt_of_flat_ne_zero _ _ _ _ _ h1
  obtain ⟨r', hr', w, hw, rfl⟩ := hS j c hjc u hu x₀ e he
  exact (DoubleCoset.eq _ _ _ _).2 ⟨(r * r')⁻¹, inv_mem (mul_mem hr hr'), w⁻¹, inv_mem hw, by group⟩

end GlobalTheory.SymChain
