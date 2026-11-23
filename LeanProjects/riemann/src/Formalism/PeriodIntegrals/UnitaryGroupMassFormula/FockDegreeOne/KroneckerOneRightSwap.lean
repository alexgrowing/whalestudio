import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OmEDiagMonomial

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.Swap

open PI.FockOneDegW PI.FockOneDegW.Diag

section Transport

variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_hwSub_iff (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (ν : Ix m n → ℚ) (w : V) :
    w ∈ hwSub act ν ↔ (∀ a, act (Eab a a) w = ((ν a : ℚ) : ℂ) • w) ∧
      ∀ a b, posC a b → act (Eab a b) w = 0 := by
  unfold hwSub wtSub
  simp [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isHW_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act ν w) : IsHW act' ν (e w) := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (he (by rw [h', map_zero])), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [hint, hmem.1 a, map_smul]
  · rw [hint, hmem.2 a b hab, map_zero]

theorem isHW_of_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (ν : Ix m n → ℚ) (w : V) (h : IsHW act' ν (e w)) : IsHW act ν w := by
  obtain ⟨h0, hmem⟩ := h
  refine ⟨fun h' => h0 (by rw [h', map_zero]), ?_⟩
  rw [mem_hwSub_iff] at hmem ⊢
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · apply he
    rw [← hint, hmem.1 a, map_smul]
  · apply he
    rw [← hint, hmem.2 a b hab, map_zero]

theorem ofType_map (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (act' : Mat m n →ₗ[ℂ] Module.End ℂ V')
    (e : V →ₗ[ℂ] V') (he : Function.Injective e) (hint : ∀ X w, act' X (e w) = e (act X w))
    (μ : Ix m n → ℚ) (v : V) (h : OfType act μ v) : OfType act' μ (e v) := by
  obtain ⟨W, hW, hv, hK, hty⟩ := h
  refine ⟨W.map e, ?_, Submodule.mem_map_of_mem hv, ?_, ?_⟩
  · exact Module.Finite.map W e
  · intro X hX w' hw'
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    rw [hint]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  · intro ν w' hw' hhw
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hw'
    exact hty ν w hw (isHW_of_map act act' e he hint ν w hhw)

end Transport

section Rename

variable {σ τ : Type*} (f : σ ≃ τ)

theorem hc_rename (φ : MvPolynomial σ ℂ) (k : ℕ) :
    homogeneousComponent k (rename f φ) = rename f (homogeneousComponent k φ) := by
  conv_lhs => rw [← sum_homogeneousComponent φ]
  rw [map_sum, map_sum]
  have h : ∀ i, homogeneousComponent k (rename f (homogeneousComponent i φ)) =
      if k = i then rename f (homogeneousComponent i φ) else 0 := fun i =>
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
      ((homogeneousComponent_isHomogeneous i φ).rename_isHomogeneous))
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp only [Finset.mem_range] at hk; omega), map_zero]

theorem minusPart_rename (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (hAB : ∀ Q, B (rename f Q) = rename f (A Q))
    (P : MvPolynomial σ ℂ) : rename f (minusPart A P) = minusPart B (rename f P) := by
  unfold minusPart
  have hfin : Function.HasFiniteSupport
      (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P))) := by
    refine (Set.finite_Iio P.totalDegree).subset ?_
    intro d hd
    by_contra h
    apply hd
    simp only [Set.mem_Iio, not_lt] at h
    simp only [homogeneousComponent_eq_zero (d + 2) P (by omega), map_zero]
  rw [map_finsum (rename f) hfin]
  refine finsum_congr fun d => ?_
  rw [← hc_rename, ← hAB, ← hc_rename]

end Rename

variable {p q r s : ℕ}

abbrev sw (p q r s : ℕ) : Ln p q r s ≃ Ln r s p q := Equiv.prodComm _ _

theorem linePos_sw (l : Ln p q r s) : linePos (sw p q r s l) = linePos l := by
  rcases l with ⟨a | a, b | b⟩ <;> rfl

theorem rename_X_mul (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (X l * P) = X (sw p q r s l) * rename (sw p q r s) P := by
  rw [map_mul, rename_X]

theorem rename_pderiv (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (pderiv l P) = pderiv (sw p q r s l) (rename (sw p q r s) P) := (pderiv_rename (sw p q r s).injective l P).symm

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (lowB l P) = lowB (sw p q r s l) (rename (sw p q r s) P) := by
  unfold lowB
  rw [linePos_sw]
  split_ifs
  · exact rename_pderiv l P
  · exact rename_X_mul l P

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (raiB l P) = raiB (sw p q r s l) (rename (sw p q r s) P) := by
  unfold raiB
  rw [linePos_sw]
  split_ifs
  · exact rename_X_mul l P
  · show rename _ (-(pderiv l P)) = -(pderiv (sw p q r s l) (rename _ P))
    rw [map_neg, rename_pderiv]

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename (sw p q r s) (omE l l' P) =
      omE (sw p q r s l) (sw p q r s l') (rename (sw p q r s) P) := by
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add, rename_raiB, rename_lowB]
  congr 1
  by_cases h : l = l'
  · subst h
    simp
  · have h' : sw p q r s l ≠ sw p q r s l' := fun e => h ((sw p q r s).injective e)
    simp [h, h']

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename (sw p q r s) (omAct p q r s M P) =
      omAct r s p q (M.submatrix (sw p q r s).symm (sw p q r s).symm) (rename (sw p q r s) P) := by
  simp only [omAct, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Matrix.entryLinearMap_apply, LinearMap.smul_apply]
  rw [map_sum]
  simp only [map_sum, map_smul, rename_omE]
  refine Fintype.sum_equiv (sw p q r s) _ _ (fun l => ?_)
  refine Fintype.sum_equiv (sw p q r s) _ _ (fun l' => ?_)
  simp [Matrix.submatrix_apply]

theorem kronecker_one_left_swap (X : Mat p q) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat r s) X).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat r s) X := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem kronecker_one_right_swap (Y : Mat r s) :
    ((Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)) (1 : Mat p q) Y).submatrix
        (sw p q r s).symm (sw p q r s).symm =
      (Matrix.kroneckerMapBilinear (LinearMap.mul ℂ ℂ)).flip (1 : Mat p q) Y := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem rename_fockAct1 (X : Mat p q) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct1 p q r s X P) = fockAct2 r s p q X (rename (sw p q r s) P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct, kronecker_one_left_swap]

theorem rename_fockAct2 (Y : Mat r s) (P : Pol p q r s) :
    rename (sw p q r s) (fockAct2 p q r s Y P) = fockAct1 r s p q Y (rename (sw p q r s) P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct, kronecker_one_right_swap]

theorem rename_sw_injective (p q r s : ℕ) :
    Function.Injective (rename (R := ℂ) (sw p q r s)) := rename_injective _ (sw p q r s).injective

def swL (p q r s : ℕ) : Pol p q r s →ₗ[ℂ] Pol r s p q := (rename (sw p q r s)).toLinearMap

theorem fock_swap_groups : Swap := by
  intro h1 p q r s μ P hP hOT hh
  have hint : ∀ (X : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q X (swL p q r s w) = swL p q r s (fockAct2 p q r s X w) :=
    fun X w => (rename_fockAct2 X w).symm
  have hOT' := ofType_map (fockAct2 p q r s) (fockAct1 r s p q) (swL p q r s)
    (rename_sw_injective p q r s) hint μ P hOT
  have hP' : rename (sw p q r s) P ≠ 0 := fun h =>
    hP (rename_sw_injective p q r s (by rw [h, map_zero]))
  have hh' : ∀ Z : Mat p q, IsPC Z → minusPart (fockAct2 r s p q Z) (rename (sw p q r s) P) = 0 := by
    intro Z hZ
    rw [← minusPart_rename (sw p q r s) (fockAct1 p q r s Z) (fockAct2 r s p q Z)
      (fun Q => (rename_fockAct1 Z Q).symm) P, hh Z hZ, map_zero]
  obtain ⟨d, hd, hmem⟩ := h1 r s p q μ (rename (sw p q r s) P) hP' hOT' hh'
  refine ⟨d, hd, ?_⟩
  have hback : rename (sw p q r s).symm (rename (sw p q r s) P) = P := by
    rw [rename_rename]
    simp
  rw [← hback]
  exact (mem_homogeneousSubmodule _ _).2
    (((mem_homogeneousSubmodule _ _).1 hmem).rename_isHomogeneous)

theorem hwHarmDeg2 (hT : HwHarmDeg) (p q r s : ℕ) (μ : Ix r s → ℚ) (e : ℕ) (v : Pol p q r s)
    (hv : v ∈ homog (Ix p q × Ix r s) e) (hw : IsHW (fockAct2 p q r s) μ v)
    (hh : ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) v = 0) :
    (e : ℚ) = degW (cPair p q) μ := by
  have hint : ∀ (X : Mat r s) (w : Pol p q r s),
      fockAct1 r s p q X (swL p q r s w) = swL p q r s (fockAct2 p q r s X w) :=
    fun X w => (rename_fockAct2 X w).symm
  have hw' := isHW_map (fockAct2 p q r s) (fockAct1 r s p q) (swL p q r s)
    (rename_sw_injective p q r s) hint μ v hw
  have hv' : rename (sw p q r s) v ∈ homog (Ix r s × Ix p q) e :=
    (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hv).rename_isHomogeneous)
  have hh' : Harm2 (rename (sw p q r s) v) := by
    intro Z hZ
    rw [← minusPart_rename (sw p q r s) (fockAct1 p q r s Z) (fockAct2 r s p q Z)
      (fun Q => (rename_fockAct1 Z Q).symm) v, hh Z hZ, map_zero]
  exact hT r s p q μ e (rename (sw p q r s) v) hv' hw' hh'

end PI.FockOneDegW.Swap
