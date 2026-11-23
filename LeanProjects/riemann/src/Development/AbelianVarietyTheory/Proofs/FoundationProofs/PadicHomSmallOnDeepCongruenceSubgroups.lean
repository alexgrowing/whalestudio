import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lam_small_of_deep_congruence : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  intro l _ Γ _ _ _ r lam hr hlam hker ε hε
  have hl : ‖((l:ℕ) : Qbar l)‖ = (l:ℝ)⁻¹ := by
    have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    simp [Padic.norm_p]
  have hl1 : ‖((l:ℕ) : Qbar l)‖ < 1 := by
    rw [hl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Set Γ := fun N => {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} ∩ {g | ε ≤ ‖(lam g).toAdd‖} with hF
  have hcm : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := (Units.continuous_val.comp hr).sub continuous_const
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    refine IsClosed.inter ?_ ?_
    · have : {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} = ⋂ i, ⋂ j, {g | ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp hcm))) continuous_const
    · exact isClosed_le continuous_const (continuous_norm.comp (continuous_toAdd.comp hlam))
  have hmono : ∀ N, F (N+1) ⊆ F N := by
    intro N g hg
    refine ⟨fun i j => (hg.1 i j).trans ?_, hg.2⟩
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ N)
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    obtain ⟨g, hg1, hg2⟩ := hcon N
    exact ⟨g, hg1, hg2.le⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hg
  have hzero : ∀ i j, ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j = 0 := by
    intro i j
    by_contra hx
    have hpos : 0 < ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ := norm_pos_iff.mpr hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hl1
    have := (hg N).1 i j
    rw [norm_pow] at this
    linarith
  have hrg : r g = 1 := by
    apply Units.ext
    have : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1 = 0 := by
      ext i j; exact hzero i j
    simpa [sub_eq_zero] using this
  have hlg : lam g = 1 := hker (MonoidHom.mem_ker.mpr hrg)
  have h2 : ε ≤ ‖(lam g).toAdd‖ := (hg 0).2
  rw [hlg] at h2
  simp at h2
  linarith
