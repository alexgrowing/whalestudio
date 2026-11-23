import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.SplitPiK

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem det_integral {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    (k.val).det ∈ 𝒪[F] ∧ ((k.val).det)⁻¹ ∈ 𝒪[F] := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have d1 : (k.val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  have d2 : ((k⁻¹).val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))
  have e : (k.val).det * ((k⁻¹).val).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp
  have e' : ((k.val).det)⁻¹ = ((k⁻¹).val).det := inv_eq_of_mul_eq_one_right e
  exact ⟨d1, e' ▸ d2⟩

theorem modulus_of_unit {u : F} (hu0 : u ≠ 0) (hu : u ∈ 𝒪[F]) (hv : u⁻¹ ∈ 𝒪[F]) : modulus u = 1 := by
  have h1 := modulus_le_one_iff.2 hu
  have h2 := modulus_le_one_iff.2 hv
  have h3 : modulus u * modulus u⁻¹ = 1 := by rw [← modulus_mul, mul_inv_cancel₀ hu0, modulus_one]
  refine le_antisymm h1 ?_
  calc (1 : NNReal) = modulus u * modulus u⁻¹ := h3.symm
    _ ≤ modulus u * 1 := mul_le_mul_of_nonneg_left h2 zero_le
    _ = modulus u := mul_one _

theorem ord_of_unit {u : F} (hu0 : u ≠ 0) (hu : u ∈ 𝒪[F]) (hv : u⁻¹ ∈ 𝒪[F]) : ord u = 0 :=
  (modulus_eq_one_iff.1 (modulus_of_unit hu0 hu hv)).2

theorem indicator_mul_unit {u : F} (hu0 : u ≠ 0) (hu : u ∈ 𝒪[F]) (hv : u⁻¹ ∈ 𝒪[F]) :
    (fun y : F × F => Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ) (y * (u, 1))) =
      Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1 := by
  funext y
  have key : y * (u, 1) ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} ↔
      y ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, mul_one]
    refine and_congr_left fun _ => ⟨fun h => ?_, fun h => mul_mem h hu⟩
    have := mul_mem h hv
    rwa [mul_assoc, mul_inv_cancel₀ hu0, mul_one] at this
  by_cases h : y ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.1 h'))]

theorem piks : Ad3.K.QuadraticBaseChangeGL3.Th.RWKS → Ad3.K.QuadraticBaseChangeGL3.Th.PIKS := by
  intro h F _ _ _ _ _ _ _ χ hχ hχ1 hcond c₁ hc k hk
  obtain ⟨d1, d2⟩ := det_integral hk
  have d0 : (k.val).det ≠ 0 := (GeneralLinearGroup.det k).ne_zero
  have hdet : ((GeneralLinearGroup.det k : Fˣ) : F) = (k.val).det :=
    Matrix.GeneralLinearGroup.val_det_apply k
  have hc1 : c₁ (GeneralLinearGroup.det k) = 1 :=
    isUnramifiedChar_iff.1 hc _ (by rw [hdet]; exact ord_of_unit d0 d1 d2)
  have hm : mp (GeneralLinearGroup.det k) (1 / 2) = 1 := by
    simp [mp, hdet, modulus_of_unit d0 d1 d2]
  have hM : (!![k.val 0 0 / (k.val).det, k.val 0 1; k.val 1 0 / (k.val).det, k.val 1 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have e := Matrix.det_fin_two k.val
    rw [Matrix.det_fin_two_of]
    field_simp
    exact e.symm
  have hI : ∀ i j, (!![k.val 0 0 / (k.val).det, k.val 0 1; k.val 1 0 / (k.val).det, k.val 1 1] :
      Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F] := by
    have h1 := ((GLnLocal.mem_integralGL_iff F 2).1 hk).1
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [div_eq_mul_inv] using mul_mem (h1 0 0) d2
    · simpa using h1 0 1
    · simpa [div_eq_mul_inv] using mul_mem (h1 1 0) d2
    · simpa using h1 1 1
  have hR := h F χ hχ hχ1 hcond _ hM hI
  funext x
  have hx := congrFun hR x
  simp only [GL2LocalData.piS, hc1, hm, Units.val_one, one_mul, indicator_mul_unit d0 d1 d2]
  simpa [GL2LocalData.rWm] using hx

end GlobalTheory.CompanionTheory.SphTheta.SplitPiK
