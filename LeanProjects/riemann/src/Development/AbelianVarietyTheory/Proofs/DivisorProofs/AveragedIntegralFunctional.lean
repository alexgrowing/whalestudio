import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.DblSiegelX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def zs {n n₁ d : ℕ} (H : Plane E n n₁) (u : Fin d → AE F E) : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
  Matrix.vecMulVec (incV F H.y) ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ u)

variable {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V] {Bf : V → V → AF F} {d : ℕ}

theorem rho_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (Φ Ψ : (κ → AF F) → ℂ) :
    dd.rho ψ w (Φ + Ψ) = dd.rho ψ w Φ + dd.rho ψ w Ψ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (w : V) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    dd.rho ψ w (c • Φ) = c • dd.rho ψ w Φ := by
  funext x; simp [Darboux.rho, schr]; ring

def avgFun (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (Φ : (κ → AF F) → ℂ) : (Fin d → AE F E) → ℂ :=
  fun u => lam (dd.rho ψ (z u) Φ)

theorem avgFun_add (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (Φ Ψ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (Φ + Ψ) = avgFun dd ψ z lam Φ + avgFun dd ψ z lam Ψ := by
  funext u; simp [avgFun, rho_add]

theorem avgFun_smul (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    avgFun dd ψ z lam (c • Φ) = c • avgFun dd ψ z lam Φ := by
  funext u; simp [avgFun, rho_smul]

def avgSub (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Integrable (avgFun dd ψ z lam Φ) μ}
  zero_mem' := by
    show Integrable (avgFun dd ψ z lam 0) μ
    have : avgFun dd ψ z lam 0 = 0 := by
      have h := avgFun_smul dd ψ z lam 0 0
      simpa using h
    rw [this]; exact integrable_zero _ _ _
  add_mem' := fun {Φ Ψ} hΦ hΨ => by
    show Integrable (avgFun dd ψ z lam (Φ + Ψ)) μ
    rw [avgFun_add]; exact hΦ.add hΨ
  smul_mem' := fun c Φ hΦ => by
    show Integrable (avgFun dd ψ z lam (c • Φ)) μ
    rw [avgFun_smul]; exact hΦ.smul c

def averagedIntegralIntegrable (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : avgSub dd ψ z lam μ →ₗ[ℂ] ℂ where
  toFun Φ := ∫ u, avgFun dd ψ z lam Φ.1 u ∂μ
  map_add' Φ Ψ := by
    simp only [Submodule.coe_add, avgFun_add, Pi.add_apply]
    exact integral_add Φ.2 Ψ.2
  map_smul' c Φ := by
    simp only [Submodule.coe_smul, avgFun_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

def avgL (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V) (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (μ : @Measure (Fin d → AE F E) (borel _)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose

theorem avgL_apply (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (z : (Fin d → AE F E) → V)
    (lam : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (μ : @Measure (Fin d → AE F E) (borel _)) (Φ : (κ → AF F) → ℂ)
    (h : Integrable (avgFun dd ψ z lam Φ) μ) : avgL dd ψ z lam μ Φ = ∫ u, avgFun dd ψ z lam Φ u ∂μ := by
  have := congrArg (fun f => f ⟨Φ, h⟩) (LinearMap.exists_extend (averagedIntegralIntegrable dd ψ z lam μ)).choose_spec
  exact this

end GlobalTheory.DblSiegelX
