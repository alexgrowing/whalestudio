import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

namespace HeckeJ

open scoped TensorProduct

section Gen

variable {L : Type*} [Field L] (σ₀ : L →+* ℂ) {WL : Type*} [AddCommGroup WL] [Module L WL]
  {H F : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup F] [Module ℂ F]
  (j : WL →ₛₗ[σ₀] H) (em : H →ₗ[ℂ] F) (TF : F →ₗ[ℂ] F) (c : ℂ)

def IsHkJ (T : WL →ₗ[L] WL) : Prop := ∀ x, em (j (T x)) = c • TF (em (j x))

open Classical in

def hLj : WL →ₗ[L] WL := if h : ∃! T, IsHkJ σ₀ j em TF c T then h.choose else 0

variable {σ₀ j em TF c}

variable (σ₀ j em TF c)

def HkJRow {Ks : Type*} [Field Ks] [Module Ks WL] (WK : Submodule Ks WL) : Prop :=
  ∃ T : WL →ₗ[L] WL, IsHkJ σ₀ j em TF c T ∧ ∀ x ∈ WK, T x ∈ WK

variable {σ₀ j em TF c}

end Gen

section Inj

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def JIndep (σ : L →+* ℂ) (jK : M →ₛₗ[σ.comp (algebraMap K L)] W) : Prop :=
  ∀ (n : ℕ) (b : Fin n → M), LinearIndependent K b → LinearIndependent ℂ fun i => jK (b i)

end Inj

end HeckeJ

end Formalism.L2.Pj
