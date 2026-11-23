import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure)
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspGA

def pos2 : Fin 2 → UPos 3 2 := ![⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]

def pos1 : Fin 2 → UPos 3 1 := ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩]

theorem second_position_bijective : Function.Bijective pos2 := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [pos2]
  · rintro ⟨⟨i, j⟩, h⟩
    fin_cases i <;> fin_cases j <;> simp at h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem first_position_bijective : Function.Bijective pos1 := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [pos1]
  · rintro ⟨⟨i, j⟩, h⟩
    fin_cases i <;> fin_cases j <;> simp at h
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem setIntegral_block {r : ℕ} (e : Fin 2 ≃ UPos 3 r) (F : (UPos 3 r → 𝔸[ℚ]) → ℂ) :
    ∫ X in unipFundamentalDomain ℚ 3 r, F X ∂unipMeasure ℚ 3 r =
      ∫ y in vecDomain ℚ (Fin 2), F (fun p => y (e.symm p)) ∂vecMeasure ℚ (Fin 2) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : UPos 3 r => GroundTheory.Global.adeleMeasure ℚ) e
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) F (unipFundamentalDomain ℚ 3 r)
  have happ : ∀ y : Fin 2 → 𝔸[ℚ],
      MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[ℚ]) e y = fun p => y (e.symm p) := by
    intro y
    funext p
    obtain ⟨i, rfl⟩ := e.surjective p
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[ℚ]) e) ⁻¹'
      unipFundamentalDomain ℚ 3 r = vecDomain ℚ (Fin 2) := by
    ext y
    simp only [Set.mem_preimage, happ, unipFundamentalDomain, vecDomain, Set.mem_univ_pi]
    exact ⟨fun hy i => by simpa using hy (e i), fun hy p => hy _⟩
  rw [← h, hpre]
  simp only [happ]

theorem unip2 (y : Fin 2 → 𝔸[ℚ]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) : G3) = uni 0 (y 0) (y 1) := by
  have h0 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(0, 2), by decide⟩ = 0 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(1, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem unip1 (y : Fin 2 → 𝔸[ℚ]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) : G3) = uni (y 0) (y 1) 0 := by
  have h0 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 1), by decide⟩ = 0 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem dia_sw_sq : dia sw * dia sw = 1 := by
  rw [dia, ← map_mul]
  have : sw * sw = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_three]
  rw [this, map_one]

theorem conj_sw (x y : 𝔸[ℚ]) : dia sw * uni x y 0 * dia sw = lowM x * uni 0 0 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sw, uni, lowM, AdelicGLn.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

theorem cusp : Ad3.GA.Cusp := by
  intro f _ hinv hY hY' r hr0 hr3 g
  have hr : r = 1 ∨ r = 2 := by omega
  rcases hr with rfl | rfl
  · have h1 : constantTerm 1 f g = ctY' f (dia sw * g) := by
      rw [constantTerm, setIntegral_block (Equiv.ofBijective pos1 first_position_bijective), ctY']
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) * g) =
        f (lowM (y 0) * uni 0 0 (y 1) * (dia sw * g))
      rw [unip1, ← conj_sw, ← hinv sw (uni (y 0) (y 1) 0 * g)]
      congr 1
      calc dia sw * (uni (y 0) (y 1) 0 * g)
          = dia sw * uni (y 0) (y 1) 0 * 1 * g := by simp only [mul_one, mul_assoc]
        _ = dia sw * uni (y 0) (y 1) 0 * dia sw * (dia sw * g) := by
            rw [← dia_sw_sq]; simp only [mul_assoc]
    rw [h1, hY']
  · have h2 : constantTerm 2 f g = ctY f g := by
      rw [constantTerm, setIntegral_block (Equiv.ofBijective pos2 second_position_bijective), ctY]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) * g) =
        f (uni 0 (y 0) (y 1) * g)
      rw [unip2]
    rw [h2, hY]

end GlobalTheory.CompanionTheory.CuspGA
