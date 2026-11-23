import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure)
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspGAK

variable (K : Type) [Field K] [NumberField K]

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

def swR (R : Type) [CommRing R] : GL (Fin 3) R :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def lowR {R : Type} [CommRing R] (c : R) : GL (Fin 3) R :=
  ⟨!![1, 0, 0; c, 1, 0; 0, 0, 1], !![1, 0, 0; -c, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem setIntegral_block {r : ℕ} (e : Fin 2 ≃ UPos 3 r) (F : (UPos 3 r → 𝔸[K]) → ℂ) :
    ∫ X in unipFundamentalDomain K 3 r, F X ∂unipMeasure K 3 r =
      ∫ y in vecDomain K (Fin 2), F (fun p => y (e.symm p)) ∂vecMeasure K (Fin 2) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : UPos 3 r => GroundTheory.Global.adeleMeasure K) e
  have h := hmp.setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) F (unipFundamentalDomain K 3 r)
  have happ : ∀ y : Fin 2 → 𝔸[K],
      MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[K]) e y = fun p => y (e.symm p) := by
    intro y
    funext p
    obtain ⟨i, rfl⟩ := e.surjective p
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : UPos 3 r => 𝔸[K]) e) ⁻¹'
      unipFundamentalDomain K 3 r = vecDomain K (Fin 2) := by
    ext y
    simp only [Set.mem_preimage, happ, unipFundamentalDomain, vecDomain, Set.mem_univ_pi]
    exact ⟨fun hy i => by simpa using hy (e i), fun hy p => hy _⟩
  rw [← h, hpre]
  simp only [happ]

theorem unip2 (y : Fin 2 → 𝔸[K]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) : AdelicGLn.AdelicGL K 3) =
      uni 0 (y 0) (y 1) := by
  have h0 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(0, 2), by decide⟩ = 0 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos2 second_position_bijective).symm ⟨(1, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos2 second_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem unip1 (y : Fin 2 → 𝔸[K]) :
    (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) : AdelicGLn.AdelicGL K 3) =
      uni (y 0) (y 1) 0 := by
  have h0 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 1), by decide⟩ = 0 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 0
  have h1 : (Equiv.ofBijective pos1 first_position_bijective).symm ⟨(0, 2), by decide⟩ = 1 :=
    (Equiv.ofBijective pos1 first_position_bijective).symm_apply_apply 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, unipMatrix, blockEntry_apply, h0, h1, Matrix.one_apply]

theorem dia_sw_sq : AdelicGLn.diagonal K 3 (swR K) * AdelicGLn.diagonal K 3 (swR K) = 1 := by
  rw [← map_mul]
  have : swR K * swR K = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swR, Matrix.mul_apply, Fin.sum_univ_three]
  rw [this, map_one]

theorem conj_sw (x y : 𝔸[K]) :
    AdelicGLn.diagonal K 3 (swR K) * uni x y 0 * AdelicGLn.diagonal K 3 (swR K) =
      lowR x * uni 0 0 y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swR, uni, lowR, AdelicGLn.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

theorem cusp_of_constantTerms (f : AdelicGLn.AdelicGL K 3 → ℂ) (hinv : IsLeftInvariant f)
    (hY : ∀ g, ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g) ∂vecMeasure K (Fin 2) = 0)
    (hY' : ∀ g, ∫ y in vecDomain K (Fin 2), f (lowR (y 0) * uni 0 0 (y 1) * g)
      ∂vecMeasure K (Fin 2) = 0) :
    IsCuspidal f := by
  intro r hr0 hr3 g
  have hr : r = 1 ∨ r = 2 := by omega
  rcases hr with rfl | rfl
  · have h1 : constantTerm 1 f g = ∫ y in vecDomain K (Fin 2),
        f (lowR (y 0) * uni 0 0 (y 1) * (AdelicGLn.diagonal K 3 (swR K) * g))
          ∂vecMeasure K (Fin 2) := by
      rw [constantTerm, setIntegral_block K (Equiv.ofBijective pos1 first_position_bijective)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos1 first_position_bijective).symm p)) * g) =
        f (lowR (y 0) * uni 0 0 (y 1) * (AdelicGLn.diagonal K 3 (swR K) * g))
      rw [unip1, ← conj_sw, ← hinv (swR K) (uni (y 0) (y 1) 0 * g)]
      congr 1
      calc AdelicGLn.diagonal K 3 (swR K) * (uni (y 0) (y 1) 0 * g)
          = AdelicGLn.diagonal K 3 (swR K) * uni (y 0) (y 1) 0 * 1 * g := by
            simp only [mul_one, mul_assoc]
        _ = AdelicGLn.diagonal K 3 (swR K) * uni (y 0) (y 1) 0 * AdelicGLn.diagonal K 3 (swR K) *
              (AdelicGLn.diagonal K 3 (swR K) * g) := by
            rw [← dia_sw_sq K]; simp only [mul_assoc]
    rw [h1, hY']
  · have h2 : constantTerm 2 f g = ∫ y in vecDomain K (Fin 2), f (uni 0 (y 0) (y 1) * g)
        ∂vecMeasure K (Fin 2) := by
      rw [constantTerm, setIntegral_block K (Equiv.ofBijective pos2 second_position_bijective)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change f (unipGL (fun p => y ((Equiv.ofBijective pos2 second_position_bijective).symm p)) * g) =
        f (uni 0 (y 0) (y 1) * g)
      rw [unip2]
    rw [h2, hY]

end GlobalTheory.CompanionTheory.CuspGAK
