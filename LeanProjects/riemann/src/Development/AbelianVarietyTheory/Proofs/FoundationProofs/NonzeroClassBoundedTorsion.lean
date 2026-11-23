import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOfMemSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem exists_bound_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E] (φ : ι → E →ₗ[K] K)
    (f : E →ₗ[K] K) (hf : f ∈ Submodule.span K (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ), 0 ≤ r → (∀ j, ‖φ j p‖ ≤ r) → ‖f p‖ ≤ C * r := by
  first
  | exact @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | (apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span ..)

theorem exists_bound_multiplier {K Γ : Type} [NormedField K] (M : Γ → Matrix (Fin 2) (Fin 2) K) (Y : Γ → Fin 2 → K)
    (hY : ¬ ∃ x : Fin 2 → K, ∀ s, Y s = M s *ᵥ x - x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : K) (x : Fin 2 → K) (r : ℝ), 0 ≤ r →
      (∀ s i, ‖(a • Y s) i - (M s *ᵥ x - x) i‖ ≤ r) → ‖a‖ ≤ C * r := by
  let φ : Γ × Fin 2 → (K × (Fin 2 → K)) →ₗ[K] K := fun j =>
    (LinearMap.proj j.2).comp (((LinearMap.fst K K (Fin 2 → K)).smulRight (Y j.1)) -
      ((Matrix.toLin' (M j.1) - LinearMap.id).comp (LinearMap.snd K K (Fin 2 → K))))
  have hφ : ∀ s i a x, φ (s, i) (a, x) = (a • Y s) i - (M s *ᵥ x - x) i := by
    intro s i a x
    simp only [φ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.id_apply, Matrix.toLin'_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hker : ⨅ j, LinearMap.ker (φ j) ≤ LinearMap.ker (LinearMap.fst K K (Fin 2 → K)) := by
    rintro ⟨a, x⟩ h
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
    simp only [LinearMap.mem_ker, LinearMap.fst_apply]
    by_contra ha
    refine hY ⟨a⁻¹ • x, fun s => ?_⟩
    have h1 : a • Y s = M s *ᵥ x - x := by
      funext i
      have := h (s, i)
      rw [hφ] at this
      exact sub_eq_zero.1 this
    rw [Matrix.mulVec_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨C, hC, h⟩ := exists_bound_of_mem_span φ _ (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  exact ⟨C, hC, fun a x r hr hb => h (a, x) r hr fun j => by rw [show j = (j.1, j.2) from rfl, hφ]; exact hb _ _⟩

theorem closed_multiplier : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  intro l hl Ω _ _ _ W c Y _ _ _ hY
  obtain ⟨C, hC, h⟩ := exists_bound_multiplier (mat W) Y (by
    rintro ⟨x, hx⟩
    refine hY ⟨x, ?_⟩
    funext s
    rw [hx s]
    simp [ReciprocityTheory.Gal.d0, Loc.colRep, Matrix.toLin'_apply])
  have hlt : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity) hlt
  refine ⟨k, fun n a _ ⟨x, _, hx⟩ => ?_⟩
  have h1 := h a x _ (norm_nonneg _) fun s i => hx s (Subgroup.mem_top s) i
  unfold Cg
  rw [sub_zero, norm_mul, norm_pow _ k]
  have h2 : C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ 1 := by
    calc C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ (C + 1) * (C + 1)⁻¹ :=
          mul_le_mul (by linarith) hk.le (by positivity) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc ‖a‖ * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((l : ℕ) : Qbar l)‖ ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖((l : ℕ) : Qbar l) ^ n‖ * (C * ‖((l : ℕ) : Qbar l)‖ ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

end GlobalTheory.Ord2.GwCount
