import Mathlib

namespace GlobalTheory

open Module

theorem exists_interpolation_basis (Y : Type) (r : ℕ) (g : Fin r → Y → ℂ) :
    ∃ (r' : ℕ) (g' : Fin r' → Y → ℂ) (c : Fin r' → Y),
    (∀ j, g' j ∈ Submodule.span ℂ (Set.range g)) ∧
    ∀ φ ∈ Submodule.span ℂ (Set.range g), ∀ y, φ y = ∑ j, φ (c j) * g' j y := by
  set V := Submodule.span ℂ (Set.range g) with hV
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  let ev : Y → Module.Dual ℂ V := fun y => (LinearMap.proj y).comp V.subtype
  have hev : ∀ y (v : V), ev y v = (v : Y → ℂ) y := fun _ _ => rfl
  have hE : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      ext y
      have := hv (ev y) (Submodule.subset_span ⟨y, rfl⟩)
      simpa [hev] using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)),
      hco, Submodule.dualAnnihilator_bot]
  obtain ⟨f, hf, hfspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range ev)
  choose c hc using hf
  let Φ : V →ₗ[ℂ] (Fin (finrank ℂ (Submodule.span ℂ (Set.range ev))) → ℂ) := LinearMap.pi (fun i => ev (c i))
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    have hle : Submodule.span ℂ (Set.range f) ≤ LinearMap.ker (Module.Dual.eval ℂ V v) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := congrFun hv i
      simp only [Φ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [← hc i]
      simpa using this
    rw [hfspan, hE] at hle
    exact (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun φ => by
      simpa using hle (Submodule.mem_top (x := φ))
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective Φ hker
  refine ⟨_, fun j => ((L (Pi.single j 1) : V) : Y → ℂ), c, fun j => (L (Pi.single j 1)).2, ?_⟩
  intro φ hφ y
  have h1 : (⟨φ, hφ⟩ : V) = L (Φ ⟨φ, hφ⟩) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  have h2 : Φ ⟨φ, hφ⟩ = ∑ j, φ (c j) • (Pi.single j 1 : Fin (finrank ℂ (Submodule.span ℂ (Set.range ev))) → ℂ) := by
    ext i
    simp [Φ, hev, Finset.sum_apply, Pi.single_apply]
  have h3 := congrArg (fun w : V => (w : Y → ℂ) y) h1
  simp only at h3
  rw [h3, h2, map_sum]
  simp [Finset.sum_apply, map_smul]

end GlobalTheory
