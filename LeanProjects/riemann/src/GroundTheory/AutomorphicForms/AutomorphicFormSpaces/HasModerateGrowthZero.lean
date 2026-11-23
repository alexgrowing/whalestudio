import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

set_option linter.unusedSectionVars false

def IsLeftInvariant (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∀ (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n), φ (AdelicGLn.diagonal K n γ * g) = φ g

def IsSmooth (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  IsArchSmooth φ ∧
    ∀ g, ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n), φ (g * finEmb K n y) = φ g

def IsKFinite (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ
    (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
      rightTranslate (k : AdelicGLn.AdelicGL K n) φ))

def IsZFinite (φ : archSmooth K n) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ
    ((fun z => uAction z φ) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n))))

def HasModerateGrowth (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ g, ‖φ g‖ ≤ C * height g ^ N

structure IsAutomorphicForm (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  isLeftInvariant : IsLeftInvariant φ
  isSmooth : IsSmooth φ
  isKFinite : IsKFinite φ
  isZFinite : IsZFinite ⟨φ, isSmooth.1⟩
  hasModerateGrowth : HasModerateGrowth φ

section Closure

variable {φ ψ : AdelicGLn.AdelicGL K n → ℂ}

theorem isLeftInvariant_zero : IsLeftInvariant (0 : AdelicGLn.AdelicGL K n → ℂ) := fun _ _ => rfl

theorem IsLeftInvariant.add (hφ : IsLeftInvariant φ) (hψ : IsLeftInvariant ψ) :
    IsLeftInvariant (φ + ψ) := fun γ g => by simp [hφ γ g, hψ γ g]

theorem IsLeftInvariant.smul (c : ℂ) (hφ : IsLeftInvariant φ) : IsLeftInvariant (c • φ) :=
  fun γ g => by simp [hφ γ g]

theorem isSmooth_zero : IsSmooth (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨(archSmooth K n).zero_mem, fun _ => Eventually.of_forall fun _ => rfl⟩

theorem IsSmooth.add (hφ : IsSmooth φ) (hψ : IsSmooth ψ) : IsSmooth (φ + ψ) :=
  ⟨(archSmooth K n).add_mem hφ.1 hψ.1, fun g => ((hφ.2 g).and (hψ.2 g)).mono fun y hy => by
    simp [hy.1, hy.2]⟩

theorem IsSmooth.smul (c : ℂ) (hφ : IsSmooth φ) : IsSmooth (c • φ) :=
  ⟨(archSmooth K n).smul_mem c hφ.1, fun g => (hφ.2 g).mono fun y hy => by simp [hy]⟩

theorem isKFinite_zero : IsKFinite (0 : AdelicGLn.AdelicGL K n → ℂ) := by
  unfold IsKFinite
  have : Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
      rightTranslate (k : AdelicGLn.AdelicGL K n) (0 : AdelicGLn.AdelicGL K n → ℂ)) ≤ ⊥ :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; simp; rfl)
  exact Submodule.finiteDimensional_of_le this

theorem IsKFinite.add (hφ : IsKFinite φ) (hψ : IsKFinite ψ) : IsKFinite (φ + ψ) := by
  unfold IsKFinite at *
  have hle : Submodule.span ℂ
      (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (φ + ψ)) ≤
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) φ) ⊔
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) ψ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem IsKFinite.smul (c : ℂ) (hφ : IsKFinite φ) : IsKFinite (c • φ) := by
  unfold IsKFinite at *
  have hle : Submodule.span ℂ
      (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) (c • φ)) ≤
      Submodule.span ℂ (range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        rightTranslate (k : AdelicGLn.AdelicGL K n) φ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem isZFinite_zero : IsZFinite (0 : archSmooth K n) := by
  unfold IsZFinite
  have : Submodule.span ℂ ((fun z => uAction z (0 : archSmooth K n)) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤ ⊥ :=
    Submodule.span_le.2 (by rintro _ ⟨z, -, rfl⟩; simp)
  exact Submodule.finiteDimensional_of_le this

theorem IsZFinite.add {φ ψ : archSmooth K n} (hφ : IsZFinite φ) (hψ : IsZFinite ψ) :
    IsZFinite (φ + ψ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (φ + ψ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ⊔
      Submodule.span ℂ ((fun z => uAction z ψ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem IsZFinite.smul (c : ℂ) {φ : archSmooth K n} (hφ : IsZFinite φ) : IsZFinite (c • φ) := by
  unfold IsZFinite at *
  have hle : Submodule.span ℂ ((fun z => uAction z (c • φ)) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) ≤
      Submodule.span ℂ ((fun z => uAction z φ) ''
        ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨z, hz, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

theorem hasModerateGrowth_zero : HasModerateGrowth (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨0, 0, fun g => by simp⟩

theorem HasModerateGrowth.add (hφ : HasModerateGrowth φ) (hψ : HasModerateGrowth ψ) :
    HasModerateGrowth (φ + ψ) := by
  obtain ⟨C₁, N₁, h₁⟩ := hφ
  obtain ⟨C₂, N₂, h₂⟩ := hψ
  refine ⟨|C₁| + |C₂|, max N₁ N₂, fun g => ?_⟩
  have hg := one_le_height g
  have e₁ : height g ^ N₁ ≤ height g ^ max N₁ N₂ := pow_le_pow_right₀ hg (le_max_left _ _)
  have e₂ : height g ^ N₂ ≤ height g ^ max N₁ N₂ := pow_le_pow_right₀ hg (le_max_right _ _)
  have p₁ : 0 ≤ height g ^ N₁ := pow_nonneg (height_pos g).le _
  have p₂ : 0 ≤ height g ^ N₂ := pow_nonneg (height_pos g).le _
  calc ‖(φ + ψ) g‖ ≤ ‖φ g‖ + ‖ψ g‖ := norm_add_le _ _
    _ ≤ C₁ * height g ^ N₁ + C₂ * height g ^ N₂ := add_le_add (h₁ g) (h₂ g)
    _ ≤ |C₁| * height g ^ max N₁ N₂ + |C₂| * height g ^ max N₁ N₂ :=
        add_le_add
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)
            (mul_le_mul_of_nonneg_left e₁ (abs_nonneg _)))
          (le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)
            (mul_le_mul_of_nonneg_left e₂ (abs_nonneg _)))
    _ = (|C₁| + |C₂|) * height g ^ max N₁ N₂ := by ring

theorem HasModerateGrowth.smul (c : ℂ) (hφ : HasModerateGrowth φ) : HasModerateGrowth (c • φ) := by
  obtain ⟨C, N, h⟩ := hφ
  refine ⟨‖c‖ * C, N, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h g) (norm_nonneg c)

theorem archSmooth_mk_add (hφ : IsArchSmooth φ) (hψ : IsArchSmooth ψ) :
    (⟨φ + ψ, (archSmooth K n).add_mem hφ hψ⟩ : archSmooth K n) = ⟨φ, hφ⟩ + ⟨ψ, hψ⟩ :=
  Subtype.ext rfl

theorem archSmooth_mk_smul (c : ℂ) (hφ : IsArchSmooth φ) :
    (⟨c • φ, (archSmooth K n).smul_mem c hφ⟩ : archSmooth K n) = c • ⟨φ, hφ⟩ :=
  Subtype.ext rfl

theorem IsAutomorphicForm.add (hφ : IsAutomorphicForm φ) (hψ : IsAutomorphicForm ψ) :
    IsAutomorphicForm (φ + ψ) where
  isLeftInvariant := hφ.isLeftInvariant.add hψ.isLeftInvariant
  isSmooth := hφ.isSmooth.add hψ.isSmooth
  isKFinite := hφ.isKFinite.add hψ.isKFinite
  isZFinite := by
    have := hφ.isZFinite.add hψ.isZFinite
    rwa [← archSmooth_mk_add] at this
  hasModerateGrowth := hφ.hasModerateGrowth.add hψ.hasModerateGrowth

theorem IsAutomorphicForm.smul (c : ℂ) (hφ : IsAutomorphicForm φ) : IsAutomorphicForm (c • φ) where
  isLeftInvariant := hφ.isLeftInvariant.smul c
  isSmooth := hφ.isSmooth.smul c
  isKFinite := hφ.isKFinite.smul c
  isZFinite := by
    have := hφ.isZFinite.smul c
    rwa [← archSmooth_mk_smul] at this
  hasModerateGrowth := hφ.hasModerateGrowth.smul c

theorem isAutomorphicForm_zero : IsAutomorphicForm (0 : AdelicGLn.AdelicGL K n → ℂ) :=
  ⟨isLeftInvariant_zero, isSmooth_zero, isKFinite_zero, isZFinite_zero, hasModerateGrowth_zero⟩

end Closure

variable (K n) in

def automorphicForms : Submodule ℂ (AdelicGLn.AdelicGL K n → ℂ) where
  carrier := {φ | IsAutomorphicForm φ}
  zero_mem' := isAutomorphicForm_zero
  add_mem' hφ hψ := hφ.add hψ
  smul_mem' c _ hφ := hφ.smul c

theorem mem_automorphicForms {φ : AdelicGLn.AdelicGL K n → ℂ} :
    φ ∈ automorphicForms K n ↔ IsAutomorphicForm φ :=
  Iff.rfl

end AutomorphicForm

end

end GroundTheory.Automorphic
