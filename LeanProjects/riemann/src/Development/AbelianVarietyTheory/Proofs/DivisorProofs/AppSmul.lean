import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ArchDecay

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def heisD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → AF F) : ℂ :=
  deriv (fun t : ℝ => M.heisLine ψ u t f x) 0

def liftI (M : Model σ X W)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun i => infAd F (ζ.1 i), fun i => infAd F (ζ.2 i))

def movI (M : Model σ X W) (p : UA σ X.J × UA σ W.J)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).1, arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).2)

def wordH (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (zs : List ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)))
    (f : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  zs.foldr (fun ζ g => heisD M ψ (liftI M ζ) g) f

end Model

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (ζ : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  dD F ζ.1 f + c • mM F (T ζ.2) f

def wordR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  zs.foldr (dR F T c) f

theorem dD_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F)
    (c : ℂ) (f : (κ → AF F) → ℂ) : dD F v (c • f) = c • dD F v f := by
  funext x
  simp only [dD, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem mM_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (c : ℂ) (f : (κ → AF F) → ℂ) : mM F l (c • f) = c • mM F l f := by
  funext x
  simp only [mM, Pi.smul_apply, smul_eq_mul]
  ring

theorem app_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (o : Op F κ) (c : ℂ)
    (f : (κ → AF F) → ℂ) : app F o (c • f) = c • app F o f := by
  cases o with
  | inl v => exact dD_smul v c f
  | inr l => exact mM_smul l c f

theorem dD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    dD F 0 f = 0 := by
  funext x
  have e : ∀ t : ℝ, (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i)) = x := by
    intro t
    funext i
    have h0 : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by unfold infAd; rw [map_zero, map_zero]; rfl
    show x i + infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i) = x i
    rw [Pi.zero_apply, smul_zero, h0, add_zero]
  show deriv (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) 0 = 0
  rw [show (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) = fun _ => f x from
    funext fun t => by rw [e t]]
  exact deriv_const 0 (f x)

theorem mM_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    mM F 0 f = 0 := by
  funext x
  simp [mM]

end GlobalTheory.ArchDecay
