import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

theorem latticeDual_int_fg {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ((latticeDual F.lattice).restrictScalars ℤ).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let ev : (Fin (r + 1) → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ v ↦ φ ⬝ᵥ (v : Fin (r + 1) → K)
      map_add' := by
        intro φ ψ
        funext v
        simp [add_dotProduct]
      map_smul' := by
        intro c φ
        funext v
        exact smul_dotProduct c φ (v : Fin (r + 1) → K) }
  have hspan : Submodule.span K (s : Set (Fin (r + 1) → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := 𝓞 K), hs, F.span_eq]
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    have h0 : ∀ w ∈ Submodule.span K (s : Set (Fin (r + 1) → K)), φ ⬝ᵥ w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact congrFun hφ ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
    funext j
    have := h0 (Pi.single j 1) (by rw [hspan]; exact Submodule.mem_top)
    simpa using this

  let T : Submodule ℤ (s → K) :=
    LinearMap.range (LinearMap.compLeft ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ) s)
  have hle : ((latticeDual F.lattice).restrictScalars ℤ).map ev ≤ T := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ v : s, (v : Fin (r + 1) → K) ∈ F.lattice := by
      intro v
      rw [← hs]
      exact Submodule.subset_span v.2
    refine ⟨fun v ↦ (hφ v (hv v)).choose, ?_⟩
    funext v
    exact (hφ v (hv v)).choose_spec
  have : IsNoetherian ℤ T := isNoetherian_of_isNoetherianRing_of_finite ℤ T
  exact Submodule.fg_of_fg_map_injective ev hinj (isNoetherian_submodule.mp inferInstance _ hle)

theorem latticeDual_ne_bot {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ∃ ψ ∈ latticeDual F.lattice, ψ ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := F.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (s.image fun v ↦ v 0)
  have hbne : algebraMap (𝓞 K) K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Pi.single 0 (algebraMap (𝓞 K) K b), ?_, fun h ↦ hbne (by simpa using congrFun h 0)⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb (x 0) (Finset.mem_image_of_mem _ hx)
    refine ⟨a, ?_⟩
    rw [ha, Algebra.smul_def]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [map_add, ha, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩

theorem DualBasisExists.proof : DualBasisExists.Statement := by
  intro K _ _ r F
  classical
  let M : Submodule ℤ (Fin (r + 1) → K) := (latticeDual F.lattice).restrictScalars ℤ
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr (latticeDual_int_fg F)
  have : Module.Free ℤ M := inferInstance
  obtain ⟨ψ, hψ, hψ0⟩ := latticeDual_ne_bot F
  have : Nontrivial M := ⟨⟨⟨ψ, hψ⟩, 0, fun h ↦ hψ0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank ℤ M := Module.finrank_pos
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℤ M = N + 1 :=
    ⟨Module.finrank ℤ M - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  let bas := Module.finBasisOfFinrankEq ℤ M hN
  refine ⟨N, fun i ↦ (bas i : Fin (r + 1) → K), ?_, ?_⟩
  · exact bas.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i ↦ (bas i : Fin (r + 1) → K)) = M.subtype '' Set.range bas := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, bas.span_eq, Submodule.map_top, Submodule.range_subtype]

end

end GroundTheory.Heights₂.Heights
