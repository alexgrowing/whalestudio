import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Mathlib
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.KMem

variable {F : Type} [Field F] [NumberField F]

theorem mem_Ohat_iff {x : Af F} : x ∈ Ohat F ↔ ∀ w, Valued.v (pLoc F w x) ≤ 1 := by
  simp only [Ohat, Subring.mem_iInf, Subring.mem_comap, ValuationSubring.mem_toSubring,
    HeightOneSpectrum.mem_adicCompletionIntegers]

theorem eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = a * b := h.symm
    _ ≤ a * 1 := by gcongr
    _ = a := mul_one a

theorem det_le {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (A : Matrix (Fin 2) (Fin 2) K) (h : ∀ i j, v (A i j) ≤ 1) : v A.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (v.map_sub _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
  · exact mul_le_one' (h 0 0) (h 1 1)
  · exact mul_le_one' (h 0 1) (h 1 0)

theorem det_mul_det_inv (g : GL (Fin 2) (Af F)) :
    (g : Matrix (Fin 2) (Fin 2) (Af F)).det * ((g⁻¹ : GL (Fin 2) (Af F)) : Matrix (Fin 2) (Fin 2) (Af F)).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

theorem v_det (g : GL (Fin 2) (Af F)) (w : HeightOneSpectrum (𝓞 F)) (h : ∀ i j, Valued.v (pLoc F w (g.val i j)) ≤ 1) :
    Valued.v (pLoc F w g.val.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact det_le _ _ h

theorem mem_KLev_iff (u : GL (Fin 2) (Af F)) :
    u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1 := by
  rw [mem_KLev]
  constructor
  · rintro ⟨ha, hb, -⟩
    have ha' : ∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1 := fun w i j => mem_Ohat_iff.1 (ha i j) w
    have hb' : ∀ w i j, Valued.v (pLoc F w ((u⁻¹ : GL (Fin 2) (Af F)).val i j)) ≤ 1 :=
      fun w i j => mem_Ohat_iff.1 (hb i j) w
    refine ⟨ha', fun w => eq_one_of_mul (v_det u w (ha' w)) (v_det _ w (hb' w)) ?_⟩
    rw [← Valuation.map_mul, ← map_mul, det_mul_det_inv, map_one, Valuation.map_one]
  · rintro ⟨ha, hd⟩
    have hinv : ∀ w, Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      intro w
      have h1 : Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det u : (Af F)ˣ) : Af F)) *
          Valued.v (pLoc F w (((Matrix.GeneralLinearGroup.det u)⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
      rw [Matrix.GeneralLinearGroup.val_det_apply, hd w, one_mul] at h1
      exact h1
    have hO : ∀ a b, u a b ∈ Ohat F := fun a b => mem_Ohat_iff.2 fun w => ha w a b
    refine ⟨hO, fun a b => mem_Ohat_iff.2 fun w => ?_, fun a b => ⟨u a b - (1 : Matrix (Fin 2) (Fin 2) (Af F)) a b, ?_, by simp⟩⟩
    · rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit,
        Matrix.smul_apply, smul_eq_mul, map_mul, Valuation.map_mul, hinv w, one_mul, Matrix.adjugate_fin_two]
      fin_cases a <;> fin_cases b <;> simp [ha w]
    · refine sub_mem (hO a b) ?_
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _

end GlobalTheory.HilbertThetaSeries.KMem

open GlobalTheory.HilbertThetaSeries.KMem in

theorem GlobalTheory.HilbertThetaSeries.kMem : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  intro F _ _
  refine ⟨mem_KLev_iff, fun u x hu hx => ⟨?_, ?_⟩, fun w g hg => ?_, fun x w => ?_, fun x => ?_⟩
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [aff, (hu w).le, hx w]
    · simp [aff, Matrix.det_fin_two, hu w]
  · refine (mem_KLev_iff _).2 ⟨fun w i j => ?_, fun w => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, (hu w).le]
    · simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, hu w]
  · obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hg
    have hk : ∀ i j, Valued.v ((k.val i j : w.adicCompletionIntegers F) : w.adicCompletion F) ≤ 1 :=
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (k.val i j).2
    refine (mem_KLev_iff _).2 ⟨fun v i j => ?_, fun v => ?_⟩
    · change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val i j) ≤ 1
      by_cases hv : v = w
      · subst hv; rw [pLoc_locGL]; exact hk i j
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    · rw [RingHom.map_det]
      change Valued.v ((Matrix.GeneralLinearGroup.map (pLoc F v) (locGL F 2 w _)).val.det) = 1
      by_cases hv : v = w
      · subst hv
        rw [pLoc_locGL]
        have e : ((Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k).val).det =
            (((Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          rw [Matrix.GeneralLinearGroup.val_det_apply]
          exact ((v.adicCompletionIntegers F).subtype.map_det k.val).symm
        rw [e]
        refine eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Matrix.GeneralLinearGroup.det k : (v.adicCompletionIntegers F)ˣ).val.2)
          ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((Matrix.GeneralLinearGroup.det k)⁻¹ : (v.adicCompletionIntegers F)ˣ).val.2) ?_
        rw [← Valuation.map_mul]
        have h := congrArg (fun y : v.adicCompletionIntegers F => (y : v.adicCompletion F)) (Matrix.GeneralLinearGroup.det k).mul_inv
        exact (congrArg Valued.v h).trans (Valuation.map_one _)
      · rw [pLoc_locGL_of_ne hv, Units.val_one, Matrix.det_one, Valuation.map_one]
  · exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  · constructor
    · intro h
      obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
      exact NumberField.RingOfIntegers.isIntegral_coe r
    · intro h w
      have e : x = algebraMap (𝓞 F) F ⟨x, h⟩ := rfl
      rw [e]
      exact HeightOneSpectrum.valuation_le_one w _

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization : ∀ (F : Type) [Field F] [NumberField F], (∀ u : GL (Fin 2) (Af F), u ∈ KLev F 2 1 ↔ (∀ w i j, Valued.v (pLoc F w (u.val i j)) ≤ 1) ∧ ∀ w, Valued.v (pLoc F w u.val.det) = 1) ∧ (∀ (u : (Af F)ˣ) (x : Af F), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) → (∀ w, Valued.v (pLoc F w x) ≤ 1) → aff u x ∈ KLev F 2 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ KLev F 2 1) ∧ (∀ w, ∀ g ∈ K1 w 0, locGL F 2 w g ∈ KLev F 2 1) ∧ (∀ (x : F) w, Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x) ∧ ∀ x : F, (∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1) ↔ IsIntegral ℤ x := by
  first | exact @GlobalTheory.HilbertThetaSeries.kMem | exact GlobalTheory.HilbertThetaSeries.kMem | (intros; apply GlobalTheory.HilbertThetaSeries.kMem <;> assumption)
