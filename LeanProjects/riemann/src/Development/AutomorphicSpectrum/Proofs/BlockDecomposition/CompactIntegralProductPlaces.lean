import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalHaarMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThird
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxCompactTransposeInvWeyl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFinitePlaneMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProduct
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
open GlobalTheory.CompanionTheory.GL2Factorization.Abs

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.Abs.KInt

open Ad3.K.GL2LocalData (rotR kR)

instance : IsFiniteMeasure rho := ⟨by rw [rho, Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩

theorem rho_univ : rho Set.univ = ENNReal.ofReal (2 * Real.pi) := by
  simp [rho]

theorem rotR_val (θ : ℝ) :
    (rotR θ).val = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  have hd : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  unfold rotR
  rw [dif_pos hd]
  rfl

def dd (ε : Bool) : ℝ := if ε then -1 else 1

theorem kR_val (θ : ℝ) (ε : Bool) :
    (kR θ ε).val = !![Real.cos θ, dd ε * Real.sin θ; -Real.sin θ, dd ε * Real.cos θ] := by
  cases ε <;>
  · simp only [kR, Units.val_mul, rotR_val, dg2, dd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_one]

theorem kR_mul (θ θ' : ℝ) (ε ε' : Bool) : kR θ ε * kR θ' ε' = kR (θ + dd ε * θ') (xor ε ε') := by
  apply Units.ext
  rw [Units.val_mul, kR_val, kR_val, kR_val]
  cases ε <;> cases ε' <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, dd, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub, ← sub_eq_add_neg] <;> ring

theorem kR_zero : kR 0 false = 1 := by
  apply Units.ext
  rw [kR_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dd]

theorem dd_mul_self (ε : Bool) : dd ε * dd ε = 1 := by cases ε <;> simp [dd]

theorem kR_inv (θ : ℝ) (ε : Bool) : (kR θ ε)⁻¹ = kR (-(dd ε * θ)) ε := by
  rw [inv_eq_iff_mul_eq_one, kR_mul]
  have : θ + dd ε * -(dd ε * θ) = 0 := by
    have := dd_mul_self ε
    linear_combination (-θ) * this
  rw [this]
  simp [kR_zero]

theorem continuous_kR (ε : Bool) : Continuous fun θ => kR θ ε := by
  have hv : Continuous fun θ => (kR θ ε).val := by
    simp only [kR_val]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun θ => ((kR θ ε)⁻¹ : GL (Fin 2) ℝ).val) = (fun θ => (kR θ ε).val) ∘ fun θ => -(dd ε * θ) := by
    funext θ
    rw [kR_inv]
    rfl
  change Continuous (fun θ => ((kR θ ε)⁻¹ : GL (Fin 2) ℝ).val)
  rw [this]
  exact hv.comp (by fun_prop)

instance : IsProbabilityMeasure orthogonalHaarMeasure := ⟨by
  unfold orthogonalHaarMeasure
  rw [Measure.smul_apply, Measure.add_apply,
    Measure.map_apply (continuous_kR false).measurable MeasurableSet.univ,
    Measure.map_apply (continuous_kR true).measurable MeasurableSet.univ]
  simp only [Set.preimage_univ, rho_univ, smul_eq_mul]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have : (4 * Real.pi)⁻¹ * (2 * Real.pi + 2 * Real.pi) = 1 := by
    have := Real.pi_pos.ne'
    field_simp
    ring
  rw [this, ENNReal.ofReal_one]⟩

open GroundTheory.Automorphic.GL2Classical (realPart realEmb realInf)

abbrev phiR : (default : InfinitePlace ℚ).Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (RationalIdeles.isReal_infinitePlace default)

section Local

variable (v : Pl)

theorem haar_maxCompact_ne_zero : LFS.hG (GP.psiF v) (GL2LocalData.K2 (Qv v)) ≠ 0 :=
  (GLnLocal.isOpen_integralGL (Qv v) 2).measure_ne_zero _ ⟨1, one_mem _⟩

theorem haar_maxCompact_ne_top : LFS.hG (GP.psiF v) (GL2LocalData.K2 (Qv v)) ≠ ⊤ :=
  (GLnLocal.isCompact_integralGL (Qv v) 2).measure_ne_top

instance : IsProbabilityMeasure (mKv v) := ⟨by
  unfold mKv
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (haar_maxCompact_ne_zero v) (haar_maxCompact_ne_top v)⟩

end Local

section Main

variable (S : Finset Pl)

def Phi (κ : KA) : GL (Fin 2) ℝ × ∀ v : S, GL (Fin 2) (Qv v.1) :=
  (realPart κ.1, fun v => finAt v.1 κ.1)

def nu : Measure (GL (Fin 2) ℝ × ∀ v : S, GL (Fin 2) (Qv v.1)) :=
  orthogonalHaarMeasure.prod (Measure.pi fun v : S => mKv v.1)

instance : IsProbabilityMeasure (nu S) := by unfold nu; infer_instance

end Main

end GlobalTheory.CompanionTheory.GL2Factorization.Abs.KInt
