import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.IsClosedDivisorComponent

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace KT

open Matrix MeasureTheory Complex Finset
open GroundTheory.Automorphic.ArchWhittaker (topologicalClosure_span_orbit eq_zero_of_forall_inner_map
  eq_smul_one_of_commute)
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate

def transposeU (k : U2) : U2 :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℂ)ᵀ, Matrix.transpose_mem_unitaryGroup_iff.2 k.2⟩

@[simp] theorem coe_transposeU (k : U2) :
    ((transposeU k : U2) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := rfl

theorem transposeU_transposeU (k : U2) : transposeU (transposeU k) = k := Subtype.ext (by simp)

theorem transposeU_mul (k l : U2) : transposeU (k * l) = transposeU l * transposeU k :=
  Subtype.ext (by simp [Matrix.transpose_mul])

theorem continuous_transposeU : Continuous transposeU :=
  Continuous.subtype_mk (continuous_subtype_val.matrix_transpose) _

def transposeHomeo : U2 ≃ₜ U2 where
  toFun := transposeU
  invFun := transposeU
  left_inv := transposeU_transposeU
  right_inv := transposeU_transposeU
  continuous_toFun := continuous_transposeU
  continuous_invFun := continuous_transposeU

theorem map_transpose_μK : Measure.map transposeU μK = μK := by
  have hmeas : Measurable transposeU := continuous_transposeU.measurable
  haveI : (Measure.map transposeU μK).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have e : (fun k => g * k) ∘ transposeU = transposeU ∘ (fun k => k * transposeU g) := by
      funext k; simp [transposeU_mul, transposeU_transposeU]
    rw [e, ← Measure.map_map hmeas (measurable_mul_const _), map_mul_right_eq_self]
  haveI : (Measure.map transposeU μK).IsHaarMeasure :=
    { lt_top_of_isCompact := fun K hK => measure_lt_top _ _
      toIsOpenPosMeasure := ⟨fun U hU hne => by
        rw [Measure.map_apply hmeas hU.measurableSet]
        exact (hU.preimage continuous_transposeU).measure_ne_zero μK
          (by obtain ⟨u, hu⟩ := hne; exact ⟨transposeU u, by simpa [transposeU_transposeU] using hu⟩)⟩ }
  haveI : IsProbabilityMeasure (Measure.map transposeU μK) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem integral_transpose_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E) :
    ∫ k, f (transposeU k) ∂μK = ∫ k, f k ∂μK := by
  have := integral_map_equiv (μ := μK) (transposeHomeo.toMeasurableEquiv) f
  have e : ((transposeHomeo.toMeasurableEquiv : U2 ≃ᵐ U2) : U2 → U2) = transposeU := rfl
  rw [e, map_transpose_μK] at this
  exact this.symm

theorem psi_transposeU_self (n : ℕ) (q : ℤ) (k : U2) : psi n q n (transposeU k) = psi n q n k := by
  simp [psi, Matrix.det_transpose]

theorem conj_psi_inv (n : ℕ) (q : ℤ) (i : ℕ) (k : U2) :
    conj (psi n q i k⁻¹) = psi n q i (transposeU k) := by
  simp only [psi, coe_inv_U2, det_star_U2, coe_transposeU, map_mul, map_pow, map_zpow₀,
    starRingEnd_self_apply, Matrix.transpose_apply, Matrix.det_transpose]
  simp [Matrix.star_apply]

theorem det_ne_zero_GL2C (g : GL2C) : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 (g : GL (Fin 2) ℂ).isUnit).ne_zero

noncomputable def iotaC (g : GL2C) : GL2C :=
  toGLC ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ (by rw [Matrix.det_transpose]; exact det_ne_zero_GL2C g)

theorem iotaC_mul (g h : GL2C) : iotaC (g * h) = iotaC h * iotaC g := by
  apply GL2C_ext; simp [iotaC, Matrix.transpose_mul]

theorem iotaC_kC (k : U2) : iotaC (kC k) = kC (transposeU k) := by
  apply GL2C_ext; simp [iotaC]

theorem iotaC_dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : iotaC (dC d₁ d₂ h₁ h₂) = dC d₁ d₂ h₁ h₂ := by
  apply GL2C_ext; simp only [iotaC, coe_toGLC, coe_dC]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_kakC (g : GL2C) : ∃ (k₁ k₂ : U2) (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂),
    g = kC k₁ * dC d₁ d₂ h₁ h₂ * kC k₂ := by
  obtain ⟨k₁, k₂, a, ha, hg⟩ := exists_KAK (g : GL (Fin 2) ℂ)
  refine ⟨k₁, k₂, a 0, a 1, ha 0, ha 1, GL2C_ext ?_⟩
  rw [hg]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_kC, coe_dC]
  congr 2
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem tC_dC_comm (a b d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    kC (tC a b) * dC d₁ d₂ h₁ h₂ = dC d₁ d₂ h₁ h₂ * kC (tC a b) := by
  apply GL2C_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_kC, coe_tC, coe_dC]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep GL2C H)

theorem inner_Q_map_dC_eq_zero (n : ℕ) (q : ℤ) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hij : i ≠ j)
    (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) (x y : H) :
    ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ = 0 := by
  have hne : ((i : ℝ) - j) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
  set a : ℝ := Real.pi / ((i : ℝ) - j) with ha
  have h1 : ⟪σ (kC (tC a 0)) (Q σ n q j y), σ (kC (tC a 0)) (σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x))⟫_ℂ =
      ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ := by
    rw [UnitaryRep.inner_map_left, ← UnitaryRep.map_mul_apply, inv_mul_cancel, UnitaryRep.map_one,
      ContinuousLinearMap.one_apply]
  have h2 : ⟪σ (kC (tC a 0)) (Q σ n q j y), σ (kC (tC a 0)) (σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x))⟫_ℂ =
      -⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ := by
    rw [← UnitaryRep.map_mul_apply, tC_dC_comm, UnitaryRep.map_mul_apply, map_tC_Q σ n q hj,
      map_tC_Q σ n q hi, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      conj_exp_mul_exp]
    have : (((i : ℝ) + q) * a + ((n : ℝ) - i + q) * 0 - (((j : ℝ) + q) * a + ((n : ℝ) - j + q) * 0)) =
        Real.pi := by
      rw [ha]; field_simp; ring
    rw [this, show Complex.exp (I * (Real.pi : ℂ)) = -1 by rw [mul_comm, Complex.exp_pi_mul_I]]
    ring
  have : (2 : ℂ) * ⟪Q σ n q j y, σ (dC d₁ d₂ h₁ h₂) (Q σ n q i x)⟫_ℂ = 0 := by
    linear_combination h1.symm.trans h2
  simpa using this

theorem inner_sum_smul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (u v : ι → H) (T : H →L[ℂ] H) :
    ⟪∑ j ∈ s, a j • u j, T (∑ i ∈ s, b i • v i)⟫_ℂ =
      ∑ j ∈ s, ∑ i ∈ s, conj (a j) * b i * ⟪u j, T (v i)⟫_ℂ := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, mul_assoc]

theorem map_kC_of_mem {n : ℕ} {q : ℤ} {x : H} (hx : x ∈ W σ n q) (l : U2) :
    σ (kC l) x = ∑ i ∈ range (n + 1),
      ((n.choose i : ℂ) * psi n q i l) • (((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x) := by
  conv_lhs => rw [← (mem_W σ).1 hx]
  rw [map_P]

theorem inner_map_kak {n : ℕ} {q : ℤ} {x y : H} (hx : x ∈ W σ n q) (hy : y ∈ W σ n q)
    (k₁ k₂ : U2) (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    ⟪y, σ (kC k₁ * dC d₁ d₂ h₁ h₂ * kC k₂) x⟫_ℂ =
      ∑ i ∈ range (n + 1), ((n.choose i : ℂ) ^ 2 * psi n q i (transposeU k₁) * psi n q i k₂) *
        ⟪((normSqInt n q)⁻¹ : ℂ) • Q σ n q i y,
          σ (dC d₁ d₂ h₁ h₂) (((normSqInt n q)⁻¹ : ℂ) • Q σ n q i x)⟫_ℂ := by
  rw [UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right,
    ← map_inv, map_kC_of_mem σ hx, map_kC_of_mem σ hy]
  rw [show (σ (dC d₁ d₂ h₁ h₂)) = (σ (dC d₁ d₂ h₁ h₂) : H →L[ℂ] H) from rfl, inner_sum_smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single j]
  · rw [map_mul, conj_psi_inv, map_natCast]; ring
  · intro i hi hij
    rw [map_smul, inner_smul_left, inner_smul_right,
      inner_Q_map_dC_eq_zero σ n q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hij]
    ring
  · intro h; exact absurd hj h

theorem inner_map_iotaC {n : ℕ} {q : ℤ} {x y : H} (hx : x ∈ W σ n q) (hy : y ∈ W σ n q) (g : GL2C) :
    ⟪y, σ (iotaC g) x⟫_ℂ = ⟪y, σ g x⟫_ℂ := by
  obtain ⟨k₁, k₂, d₁, d₂, h₁, h₂, rfl⟩ := exists_kakC g
  rw [iotaC_mul, iotaC_mul, iotaC_kC, iotaC_kC, iotaC_dC, ← mul_assoc, inner_map_kak σ hx hy,
    inner_map_kak σ hx hy, transposeU_transposeU]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

instance completeSpace_alt (n : ℕ) (q : ℤ) : CompleteSpace (W σ n q) :=
  (isClosed_divisorComponent σ n q).completeSpace_coe

noncomputable def compr (n : ℕ) (q : ℤ) (g : GL2C) : W σ n q →L[ℂ] W σ n q :=
  ((PL σ n q).comp ((σ g).comp (W σ n q).subtypeL)).codRestrict (W σ n q)
    (fun _ => P_mem_alt σ n q _)

@[simp] theorem coe_compr_apply (n : ℕ) (q : ℤ) (g : GL2C) (v : W σ n q) :
    ((compr σ n q g v : W σ n q) : H) = P σ n q (σ g v) := rfl

theorem inner_compr (n : ℕ) (q : ℤ) (g : GL2C) (v w : W σ n q) :
    ⟪(w : H), (compr σ n q g v : H)⟫_ℂ = ⟪(w : H), σ g v⟫_ℂ := by
  rw [coe_compr_apply, inner_P_of_mem σ w.2]

theorem inner_compr_compr (n : ℕ) (q : ℤ) (g h : GL2C) (v w : W σ n q) :
    ⟪(w : H), (compr σ n q g (compr σ n q h v) : H)⟫_ℂ = ((normSqInt n q)⁻¹ : ℂ) *
      ∫ k, conj (psi n q n k) * ⟪(w : H), σ (g * kC k * h) v⟫_ℂ ∂μK := by
  rw [inner_compr, coe_compr_apply, UnitaryRep.inner_map_right, P, inner_smul_right, Q,
    inner_Kint_right σ (continuous_conj_psi n q n)]
  congr 1
  congr 1; funext k
  rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply,
    mul_assoc]

theorem compr_iotaC (n : ℕ) (q : ℤ) (g : GL2C) : compr σ n q (iotaC g) = compr σ n q g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, inner_compr, inner_compr,
    inner_map_iotaC σ v.2 w.2]

theorem compr_comm (n : ℕ) (q : ℤ) (g h : GL2C) :
    compr σ n q g * compr σ n q h = compr σ n q h * compr σ n q g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, inner_compr_compr, ← compr_iotaC σ n q h, ← compr_iotaC σ n q g,
    inner_compr_compr]
  congr 1
  set F : U2 → ℂ := fun k => conj (psi n q n k) * ⟪(w : H), σ (iotaC h * kC k * iotaC g) v⟫_ℂ with hF
  rw [← integral_transpose_K F]
  congr 1; funext k
  simp only [hF]
  rw [psi_transposeU_self, ← iotaC_kC, ← inner_map_iotaC σ v.2 w.2 (g * kC k * h), iotaC_mul,
    iotaC_mul]
  simp only [mul_assoc]

end KT

end GroundTheory.Automorphic.ArchWhittakerC
