import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.PerFix

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l) : ‖σ y‖ = ‖y‖ :=
  (spectralNorm_eq_of_equiv σ y).symm

def inertiaC (c : Coef l) : Subgroup (Qbar l ≃ₐ[ℚ_[l]] Qbar l) where
  carrier := {σ | (∀ b ∈ c.O, σ b = b) ∧ ∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := ⟨fun b _ => rfl, fun y _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ (τ b) = b
      rw [hτ1 b hb, hσ1 b hb]
    · show ‖σ (τ y) - y‖ < 1
      have e : σ (τ y) - y = (σ (τ y) - τ y) + (τ y - y) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hσ2 _ ((norm_aut τ y).le.trans hy)) (hτ2 y hy))
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ.symm b = b
      exact σ.symm_apply_eq.2 (hσ1 b hb).symm
    · show ‖σ.symm y - y‖ < 1
      have e : σ.symm y - y = σ.symm (y - σ y) := by simp
      rw [e, norm_aut, norm_sub_rev]
      exact hσ2 y hy

theorem exists_fixed_near : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  intro l _ c
  obtain ⟨C, -, hC⟩ := GlobalTheory.AxLemma.ax_lemma l
  have hl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    rw [show ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : Qbar l) from (map_natCast _ _).symm,
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c₁, fun k x hx hfix => ?_⟩
  by_cases hk : k ≤ c₁
  · refine ⟨0, by simp, fun σ _ _ => map_zero σ, ?_⟩
    have h0 : k - c₁ = 0 := by omega
    simpa [Cg, h0] using hx
  · obtain ⟨y, hyH, hxy⟩ := hC (inertiaC c) x ‖((l : ℕ) : Qbar l) ^ k‖ (fun g hg => hfix g hg.1 hg.2)
    have hlpos : (0 : ℝ) < l := by linarith
    have key : C * ‖((l : ℕ) : Qbar l) ^ k‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ := by
      rw [norm_pow, norm_pow, hl]
      have e : (l : ℝ)⁻¹ ^ k = (l : ℝ)⁻¹ ^ (k - c₁) * (l : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm, mul_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hxy' := hxy.trans key
    have hle1 : ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ ≤ 1 := by
      rw [norm_pow, hl]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)
    refine ⟨y, ?_, fun σ h1 h2 => hyH σ ⟨h1, h2⟩, hxy'⟩
    have e : y = x + (y - x) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ((norm_sub_rev y x).le.trans (hxy'.trans hle1)))

end GlobalTheory.PerFix
