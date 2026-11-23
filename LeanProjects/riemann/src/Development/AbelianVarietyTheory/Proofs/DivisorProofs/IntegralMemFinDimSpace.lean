import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem integral_mem_of_finiteDimensional_fun {X Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (V : Submodule ℂ (X → ℂ)) (hV : FiniteDimensional ℂ V)
    (Fm : Y → X → ℂ) (hFm : ∀ y, Fm y ∈ V) (hint : ∀ x, Integrable (fun y => Fm y x) μ) :
    (fun x => ∫ y, Fm y x ∂μ) ∈ V := by
  classical
  let G : Y → V := fun y => ⟨Fm y, hFm y⟩
  let ev : X → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp V.subtype
  have hev : ∀ x v, ev x v = (v : X → ℂ) x := fun x v => rfl
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      ext x
      have := hv (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0]
    exact Submodule.dualAnnihilator_bot
  let P : Submodule ℂ (Module.Dual ℂ V) :=
    { carrier := {φ | Integrable (fun y => φ (G y)) μ}
      add_mem' := fun {a b} ha hb => by
        show Integrable (fun y => a (G y) + b (G y)) μ
        exact ha.add hb
      zero_mem' := by simp
      smul_mem' := fun c φ hφ => by simpa using hφ.const_mul c }
  have hP : ∀ φ : Module.Dual ℂ V, Integrable (fun y => φ (G y)) μ := by
    intro φ
    have hle : Submodule.span ℂ (Set.range ev) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hint x
    exact hle (hspan ▸ Submodule.mem_top)
  let b := Module.finBasis ℂ V
  let E := b.equivFun
  have hEi : Integrable (fun y => E (G y)) μ := by
    rw [integrable_pi_iff]
    intro j
    simpa [E] using hP (b.coord j)
  set c := ∫ y, E (G y) ∂μ
  have key : ∀ x, ∫ y, Fm y x ∂μ = ((E.symm c : V) : X → ℂ) x := by
    intro x
    let ℓ : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((ev x).comp E.symm.toLinearMap)
    have h1 := ℓ.integral_comp_comm hEi
    have h2 : ∀ y, ℓ (E (G y)) = Fm y x := by intro y; simp [ℓ, hev, G]
    simp only [h2] at h1
    rw [h1]
    rfl
  have : (fun x => ∫ y, Fm y x ∂μ) = ((E.symm c : V) : X → ℂ) := funext key
  rw [this]
  exact (E.symm c).2

example : ∀ {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (V : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ V →
  ∀ Fm : Y → X → ℂ, (∀ y, Fm y ∈ V) → (∀ x, Integrable (fun y => Fm y x) μ) → (fun x => ∫ y, Fm y x ∂μ) ∈ V :=
  @integral_mem_of_finiteDimensional_fun

end GlobalTheory
