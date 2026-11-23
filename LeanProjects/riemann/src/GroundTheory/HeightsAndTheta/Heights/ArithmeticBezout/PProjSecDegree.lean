import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjSecDegree

variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)

set_option hygiene false in

local notation "𝕂" => FractionRing (MvPolynomial (Fin (e + 1)) ℂ)

set_option hygiene false in

local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ

theorem projVar_ne_zero (i : Fin (e + 1)) : projVar e i ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective ℝt 𝕂)).2 (X_ne_zero i)

theorem algebraMap_C (c : ℂ) : algebraMap ℝt 𝕂 (C c) = algebraMap ℂ 𝕂 c := by
  rw [IsScalarTower.algebraMap_apply ℂ ℝt 𝕂 c, MvPolynomial.algebraMap_eq]

theorem chartForm_projPar :
    Vertical.chartForm (projPar A) =
      C (projVar e 0)⁻¹ * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) := by
  simp only [Vertical.chartForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, div_eq_inv_mul]

theorem secForm_projPar (i : Fin e) :
    Vertical.secForm (projPar A) i =
      C (projVar e i.succ) * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) -
        C (projVar e 0) * (ComplexSets.linPoly A i.succ).map (algebraMap ℂ 𝕂) := by
  simp only [Vertical.secForm, linForm, projPar, ComplexSets.linPoly, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_sub, C_mul, C_mul]
  ring

theorem projHom_C (c : ℂ) : ComplexSets.projHom J A (C c) = Ideal.Quotient.mk J (C c) := by
  simp [ComplexSets.projHom, ComplexSets.pullback]
  rfl

theorem projHom_X (i : Fin (e + 1)) :
    ComplexSets.projHom J A (X i) = Ideal.Quotient.mk J (ComplexSets.linPoly A i) := by
  simp [ComplexSets.projHom, ComplexSets.pullback]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem finrank_eq [Algebra ℝt (MvPolynomial (Fin n) ℂ ⧸ J)]
    (hφ : ∀ p, algebraMap ℝt (MvPolynomial (Fin n) ℂ ⧸ J) p = ComplexSets.projHom J A p) :
    Module.finrank 𝕂 (TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J)) =
      Module.finrank 𝕂
        (Vertical.SecAlg (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)) := by
  let I := Vertical.secIdeal (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)
  let σ : MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin n) 𝕂 := MvPolynomial.map (algebraMap ℂ 𝕂)
  have hmkC : ∀ k : 𝕂, Ideal.Quotient.mk I (C k) = algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) k :=
    fun _ => rfl
  have hmem : ∀ x ∈ I, Ideal.Quotient.mk I x = 0 := fun _ h => Ideal.Quotient.eq_zero_iff_mem.2 h

  have hunit : IsUnit (algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0)) :=
    (IsUnit.mk0 _ (projVar_ne_zero 0)).map _
  have ha0 : Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e 0) := by
    have h := hmem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rw [chartForm_projPar, map_sub, map_mul, map_one, hmkC, sub_eq_zero] at h
    calc _ = algebraMap 𝕂 _ (projVar e 0) * (algebraMap 𝕂 _ (projVar e 0)⁻¹ *
          Ideal.Quotient.mk I (σ (ComplexSets.linPoly A 0))) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (projVar_ne_zero _), map_one, one_mul]
      _ = _ := by rw [h, mul_one]
  have ha : ∀ i, Ideal.Quotient.mk I (σ (ComplexSets.linPoly A i)) =
      algebraMap 𝕂 (MvPolynomial (Fin n) 𝕂 ⧸ I) (projVar e i) := by
    refine Fin.cases ha0 fun i => ?_
    have h := hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
    rw [secForm_projPar, map_sub, map_mul, map_mul, hmkC, hmkC, ha0, sub_eq_zero] at h
    exact hunit.mul_left_cancel (h.symm.trans (mul_comm _ _))

  let ψ : MvPolynomial (Fin n) ℂ ⧸ J →+* MvPolynomial (Fin n) 𝕂 ⧸ I :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk I).comp σ) fun p hp =>
      hmem _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
  have hψ : ψ.comp (algebraMap ℝt _) = algebraMap ℝt (MvPolynomial (Fin n) 𝕂 ⧸ I) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, hφ, projHom_C, Ideal.Quotient.lift_mk, RingHom.comp_apply,
        MvPolynomial.map_C, hmkC, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · rw [RingHom.comp_apply, hφ, projHom_X, Ideal.Quotient.lift_mk, RingHom.comp_apply, ha,
        IsScalarTower.algebraMap_apply ℝt 𝕂]
      rfl
  let g : (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℝt] MvPolynomial (Fin n) 𝕂 ⧸ I :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  let F := AlgHom.liftEquiv ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) (MvPolynomial (Fin n) 𝕂 ⧸ I) g

  let G₀ : MvPolynomial (Fin n) 𝕂 →ₐ[𝕂] TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J) :=
    aeval fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)
  have hG : G₀.toRingHom.comp σ =
      ((Algebra.TensorProduct.includeRight (R := ℝt) (A := 𝕂)).toRingHom).comp
        (Ideal.Quotient.mk J) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, σ,
        MvPolynomial.map_C, G₀, aeval_C]
      rw [← projHom_C J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, algebraMap_C]
    · simp [G₀, σ]
  have hGa : ∀ i, G₀ (σ (ComplexSets.linPoly A i)) = G₀ (C (projVar e i)) := by
    intro i
    have h := RingHom.congr_fun hG (ComplexSets.linPoly A i)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h
    rw [h, ← projHom_X J A, ← hφ, AlgHom.commutes, IsScalarTower.algebraMap_apply ℝt 𝕂, aeval_C]
    rfl
  have hker : I ≤ RingHom.ker G₀ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (G₀.toRingHom.comp σ) p = 0
      rw [hG, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, secForm_projPar, map_sub, map_mul, map_mul, aeval_C,
        aeval_C]
      change _ * G₀ (σ _) - _ * G₀ (σ _) = 0
      rw [hGa, hGa, aeval_C, aeval_C, ← map_mul, ← map_mul, mul_comm (projVar e i.succ), sub_self]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, chartForm_projPar, ← C_1, map_sub,
        map_mul, aeval_C, aeval_C]
      change _ * G₀ (σ _) - _ = 0
      rw [hGa, aeval_C, ← map_mul, inv_mul_cancel₀ (projVar_ne_zero _), sub_self]
  let G := Ideal.Quotient.liftₐ I G₀ fun a ha => (RingHom.mem_ker).1 (hker ha)
  have h₁ : F.comp G = AlgHom.id 𝕂 _ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro j
    change F (G₀ (X j)) = Ideal.Quotient.mk I (X j)
    simp only [G₀, aeval_X, F, AlgHom.liftEquiv_tmul, one_smul]
    change ψ (Ideal.Quotient.mk J (X j)) = _
    simp only [ψ, Ideal.Quotient.lift_mk, RingHom.comp_apply, σ, MvPolynomial.map_X]
  have h₂ : G.comp F = AlgHom.id 𝕂 _ := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    apply AlgHom.coe_ringHom_injective
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_))
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← projHom_C J A, ← hφ, AlgHom.coe_toRingHom,
        AlgHom.coe_toRingHom, AlgHom.commutes, AlgHom.commutes]
    · simp only [F, G, G₀, g, ψ, σ, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
        AlgHom.liftEquiv_tmul, one_smul, AlgHom.coe_id, id_eq, AlgHom.coe_mk, Ideal.Quotient.lift_mk,
        MvPolynomial.map_X]
      change G (Ideal.Quotient.mk I (X j)) = _
      exact aeval_X (R := 𝕂) (fun j => (1 : 𝕂) ⊗ₜ[ℝt] Ideal.Quotient.mk J (X j)) j
  exact (AlgEquiv.ofAlgHom G F h₂ h₁).toLinearEquiv.finrank_eq.symm

end ProjSecDegree

theorem ProjSecDegree.proof : ProjSecDegree.Statement := by
  intro n e J A
  let : Algebra (MvPolynomial (Fin (e + 1)) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J A).toRingHom.toAlgebra
  exact ProjSecDegree.finrank_eq J A fun _ => rfl

end

end GroundTheory.Heights₂.Heights
