import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

def stdE : LinearMap.BilinForm ℤ (Fin 2 → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => x 1 * y 0 - x 0 * y 1)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem stdE_apply (x y : Fin 2 → ℤ) : stdE x y = x 1 * y 0 - x 0 * y 1 := rfl

theorem stdE_bij : Function.Bijective stdE := by
  constructor
  · intro x y h
    have h0 := LinearMap.congr_fun h ![1, 0]
    have h1 := LinearMap.congr_fun h ![0, 1]
    simp [stdE_apply] at h0 h1
    funext i
    fin_cases i <;> simp [h0, h1]
  · intro f
    refine ⟨![-f ![0, 1], f ![1, 0]], ?_⟩
    refine LinearMap.ext fun y => ?_
    have hy : y = y 0 • ![1, 0] + y 1 • ![0, 1] := by
      funext i
      fin_cases i <;> simp
    conv_rhs => rw [hy, map_add, map_smul, map_smul]
    simp [stdE_apply]
    ring

def per (w : Fin 1 → ℂ) : (Fin 2 → ℤ) →+ (Fin 1 → ℂ) where
  toFun x := fun _ => (x 0 : ℂ) + (x 1 : ℂ) * (w 0 / (2 * Real.pi * Complex.I))
  map_zero' := by funext; simp
  map_add' x y := by funext; simp; ring

theorem per_apply (w : Fin 1 → ℂ) (x : Fin 2 → ℤ) (j : Fin 1) :
    per w x j = (x 0 : ℂ) + (x 1 : ℂ) * (w 0 / (2 * Real.pi * Complex.I)) := rfl

def mon : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x 0 + x 1, x 1]
  map_add' x y := by funext i; fin_cases i <;> simp; ring
  map_smul' c x := by funext i; fin_cases i <;> simp; ring

theorem log_exp (w : Fin 1 → ℂ) : Real.log ‖expCover 1 w 0‖ = (w 0).re := by
  simp [expCover, Complex.norm_exp]

def tate : LogPeriods 1 1 1 (Fin 2 → ℤ) where
  a_le := le_rfl
  free := inferInstance
  fin := inferInstance
  rank := by simp
  E := stdE
  alt x := by rw [stdE_apply]; ring
  unimod := stdE_bij
  P := per
  hol x := by
    apply Differentiable.differentiableOn
    rw [differentiable_pi]
    intro j
    simp only [per_apply]
    fun_prop
  H z := fun _ _ => ((-(2 * Real.pi) / Real.log ‖z 0‖ : ℝ) : ℂ)
  herm w _ := by
    ext i j
    exact Complex.conj_ofReal _
  pos w hw z hz := by
    have h0 := hw.1 0
    simp only [Fin.castLE_refl] at h0
    have hz0 : z 0 ≠ 0 := fun h => hz (funext fun i => by fin_cases i; simpa using h)
    have hc : 0 < -(2 * Real.pi) / (w 0).re := div_pos_of_neg_of_neg (by linarith [Real.pi_pos]) h0
    have hn : 0 < Complex.normSq (z 0) := Complex.normSq_pos.mpr hz0
    simp only [dotProduct, mulVec, Fin.sum_univ_one, log_exp, Pi.star_apply, Complex.star_def]
    generalize -(2 * Real.pi) / (w 0).re = c at hc
    have : (z 0 * ((c : ℂ) * (starRingEnd ℂ) (z 0))).re = c * Complex.normSq (z 0) := by
      simp [Complex.normSq_apply]; ring
    rw [this]; positivity
  im w hw x y := by
    have h0 := hw.1 0
    simp only [Fin.castLE_refl] at h0
    have hτ := im_div_two_pi_I (w 0)
    simp only [dotProduct, mulVec, Fin.sum_univ_one, log_exp, Pi.star_apply, Complex.star_def,
      per_apply, stdE_apply]
    generalize w 0 / (2 * Real.pi * Complex.I) = t at hτ
    have hc : -(2 * Real.pi) / (w 0).re * t.im = 1 := by
      have := Real.pi_ne_zero
      have := h0.ne
      rw [hτ]; field_simp
    generalize -(2 * Real.pi) / (w 0).re = c at hc
    simp
    linear_combination ((x 1 : ℝ) * y 0 - x 0 * y 1) * hc
  T _ := mon
  mono i w _ x := by
    fin_cases i
    funext j
    simp [per_apply, mon, add_div, div_self two_pi_I_ne_zero]
    ring
  W := LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1)
  coiso x hx := by
    refine ⟨1, one_ne_zero, ?_⟩
    have := hx ![1, 0] (by simp)
    simpa [stdE_apply] using this
  s x := fun _ _ => ((x.1 0 : ℤ) : ℂ)
  s_hol _ := differentiableOn_const _
  s_eq x w _ := by
    have : x.1 1 = 0 := LinearMap.mem_ker.mp x.2
    funext j
    simp [per_apply, this]
  span := by
    rw [eq_top_iff]
    intro v _
    have : v = v 0 • (fun _ => ((((⟨![1, 0], by simp⟩ :
        LinearMap.ker (LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1)).1 0 : ℤ)) : ℂ)) := by
      funext i; fin_cases i; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem tate_T_ne : tate.T 0 ≠ LinearMap.id := by
  intro h
  have := congrFun (LinearMap.congr_fun h ![0, 1]) 0
  simp [tate, mon] at this

theorem P_injective {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : LogPeriods n a g Λ)
    {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  refine LinearMap.ext fun y => ?_
  have := L.im w hw x y
  rw [hx] at this
  simp only [zero_dotProduct, Complex.zero_im] at this
  simp only [map_zero, LinearMap.zero_apply]
  exact_mod_cast this.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel
