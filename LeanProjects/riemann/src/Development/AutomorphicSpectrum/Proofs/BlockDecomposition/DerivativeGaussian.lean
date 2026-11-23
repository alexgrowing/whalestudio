import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.TemperedDerivatives.StepsD
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open Ad3.K.LC

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementGaussK

abbrev CIdx : Type := Fin 2 × Fin 3 ⊕ Fin 2

abbrev RIdx : Type := CIdx × Bool

def cz : CIdx → (M23 × (Fin 2 → ℂ)) →ₗ[ℝ] ℂ
  | .inl (r, c) => (LinearMap.proj c) ∘ₗ (LinearMap.proj r) ∘ₗ (LinearMap.fst ℝ M23 (Fin 2 → ℂ))
  | .inr a => (LinearMap.proj a) ∘ₗ (LinearMap.snd ℝ M23 (Fin 2 → ℂ))

def rc : Bool → ℂ →ₗ[ℝ] ℝ
  | false => Complex.reLm
  | true => Complex.imLm

def toEuc : (M23 × (Fin 2 → ℂ)) →ₗ[ℝ] EuclideanSpace ℝ RIdx :=
  (WithLp.linearEquiv 2 ℝ (RIdx → ℝ)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => Real.sqrt 2 • (rc i.2 ∘ₗ cz i.1)

theorem toEuc_apply (p : M23 × (Fin 2 → ℂ)) (i : RIdx) :
    toEuc p i = Real.sqrt 2 * rc i.2 (cz i.1 p) := by
  simp [toEuc]

theorem toEuc_injective : Function.Injective toEuc := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have key : ∀ i : CIdx, cz i p = 0 := by
    intro i
    have h0 := toEuc_apply p (i, false)
    have h1 := toEuc_apply p (i, true)
    rw [hp] at h0 h1
    simp only [PiLp.zero_apply] at h0 h1
    apply Complex.ext
    · have := (mul_eq_zero.1 h0.symm).resolve_left hs
      simpa [rc] using this
    · have := (mul_eq_zero.1 h1.symm).resolve_left hs
      simpa [rc] using this
  refine Prod.ext ?_ ?_
  · funext r c
    simpa [cz] using key (.inl (r, c))
  · funext a
    simpa [cz] using key (.inr a)

theorem finrank_eq :
    Module.finrank ℝ (M23 × (Fin 2 → ℂ)) = Module.finrank ℝ (EuclideanSpace ℝ RIdx) := by
  simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]

def euc : (M23 × (Fin 2 → ℂ)) ≃L[ℝ] EuclideanSpace ℝ RIdx :=
  (LinearMap.linearEquivOfInjective toEuc toEuc_injective finrank_eq).toContinuousLinearEquiv

theorem euc_apply (p : M23 × (Fin 2 → ℂ)) : euc p = toEuc p := rfl

theorem euc_norm_sq (p : M23 × (Fin 2 → ℂ)) :
    ‖euc p‖ ^ 2 = 2 * (∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [euc_apply, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [toEuc_apply, Fintype.sum_bool, Real.norm_eq_abs, sq_abs, mul_pow, hs, rc, cz, hz,
    mul_add, Finset.mul_sum]
  simp [Finset.sum_add_distrib]
  ring

def gaussK : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euc
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ RIdx))

theorem gaussK_apply (p : M23 × (Fin 2 → ℂ)) :
    gaussK p = Complex.exp (-(2 * Real.pi : ℂ) *
      ((∑ r, ∑ c, ‖p.1 r c‖ ^ 2 + ∑ a, ‖p.2 a‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gaussK, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, euc_norm_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def polyK (k : ℕ) (p : M23 × (Fin 2 → ℂ)) : ℂ :=
  (crd 0 0 p * crd 1 1 p - crd 0 1 p * crd 1 0 p) ^ (2 * k - 2) *
    (crqc 0 p * crdc 0 0 p + crqc 1 p * crdc 1 0 p) ^ (4 * k - 4)

theorem polyK_temperate (k : ℕ) : (polyK k).HasTemperateGrowth := by
  have h1 : (fun p => crd 0 0 p * crd 1 1 p - crd 0 1 p * crd 1 0 p).HasTemperateGrowth :=
    ((crd_temperate 0 0).mul (crd_temperate 1 1)).sub ((crd_temperate 0 1).mul (crd_temperate 1 0))
  have h2 : (fun p => crqc 0 p * crdc 0 0 p + crqc 1 p * crdc 1 0 p).HasTemperateGrowth :=
    ((crqc_temperate 0).mul (crdc_temperate 0 0)).add ((crqc_temperate 1).mul (crdc_temperate 1 0))
  exact (h1.pow _).mul (h2.pow _)

theorem dGauK : DGau := fun k =>
  ⟨SchwartzMap.smulLeftCLM ℂ (polyK k) gaussK, fun p => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (polyK_temperate k), gaussK_apply, smul_eq_mul]
    simp [polyK, gauK, crd, crdc, crqc, map_add, map_mul]⟩

end GlobalTheory.CompanionTheory.GodementGaussK
