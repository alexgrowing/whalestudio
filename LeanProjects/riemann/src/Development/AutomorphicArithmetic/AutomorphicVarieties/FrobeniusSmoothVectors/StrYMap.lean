import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

noncomputable section

namespace UpperTheory.V.Fr.Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (M : Type) [AddCommGroup M] [Module k M]

def strY : Submodule k (F.G0 → M) where
  carrier := {y | IsLocallyConstant y ∧ (∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h) ∧
    y F.g0 = y (F.star F.g0) ∧
    (∀ v, ∃ α : M, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α) ∧
    ∀ v, ∃ β : M, ∀ s, y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun g h => ?_, by simp [a3, b3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
    · obtain ⟨α, h⟩ := a5 v
      obtain ⟨α', h'⟩ := b5 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, rfl, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, by simp [a3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩
    · obtain ⟨α, h⟩ := a5 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

def strS : Submodule k (F.G0 → M) where
  carrier := {a | IsLocallyConstant a ∧
    (∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + (((F.Ψ g)⁻¹ : kˣ) : k) • a h) ∧ (∀ g, a (F.star g) = a g) ∧
    ∀ v, ∃ γ : M, ∀ s, a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => by simp [a3, b3], fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, fun g => by simp [a3], fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

variable {F M} {M' : Type} [AddCommGroup M'] [Module k M']

theorem strY_map (f : M →ₗ[k] M') {y : F.G0 → M} (hy : y ∈ F.strY M) : (fun g => f (y g)) ∈ F.strY M' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨h1.comp f, fun g h => ?_, congrArg f h3, fun v => ?_, fun v => ?_⟩
  · simp only [h2, map_add, map_smul]
  · obtain ⟨α, hα⟩ := h4 v
    exact ⟨f α, fun s => by simp only [hα, map_smul]⟩
  · obtain ⟨β, hβ⟩ := h5 v
    exact ⟨f β, fun s => by simp only [hβ, map_smul]⟩

theorem strS_map (f : M →ₗ[k] M') {a : F.G0 → M} (ha : a ∈ F.strS M) : (fun g => f (a g)) ∈ F.strS M' := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1.comp f, fun g h => ?_, fun g => congrArg f (h3 g), fun v => ?_⟩
  · simp only [h2, map_add, map_smul]
  · obtain ⟨γ, hγ⟩ := h4 v
    exact ⟨f γ, fun s => by simp only [hγ, map_smul]⟩

end UpperTheory.V.Fr.Frame
