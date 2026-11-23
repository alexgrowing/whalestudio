import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfEtaSp

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem etaIn_holds : EtaIn σ J ψ v := by
  intro hstd hun hp e hee
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  have hsp := thetaSpan_holds σ J ψ v hstd hun θ h4
  have hind := theta_indep σ v hstd.1 θ h3
  set iθ : Fv F v ⊗[F] E := inclR (F := F) (Fv F v) (θ : E) with hiθ
  have scm : ∀ a b : Fv F v, sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := fun a b => by
    simp only [sc_eq', map_mul]
  have hcoord : ∀ y : Fv F v ⊗[F] E, ∃ c0 c1 : Fv F v, y = sc (E := E) v c0 + sc (E := E) v c1 * iθ := by
    have hnot : ∀ c : F, algebraMap F E c ≠ (θ : E) := by
      intro c hc
      have hint : IsIntegral ℤ c := by
        rw [← isIntegral_algebraMap_iff (A := F) (B := E) (FaithfulSMul.algebraMap_injective F E), hc]
        exact θ.isIntegral_coe
      let c' : 𝓞 F := ⟨c, (mem_integralClosure_iff ℤ F).2 hint⟩
      have hθ : algebraMap (𝓞 F) (𝓞 E) c' = θ := RingOfIntegers.ext hc
      have := (h3 (Ideal.Quotient.mk _ c') (-1) (by
        rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hθ, map_neg, map_one]; ring)).2
      exact one_ne_zero (neg_eq_zero.1 this)
    have li : LinearIndependent F ![(1 : E), (θ : E)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
        exact ⟨hst, rfl⟩
      · exfalso
        apply hnot (-(t⁻¹ * s))
        have hy' : (θ : E) = t⁻¹ • (t • (θ : E)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [hy', eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]
    let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank li (by simpa using hstd.1.2.2.1.symm)
    let B := Algebra.TensorProduct.basis (Fv F v) b
    have hB0 : B 0 = (1 : Fv F v) ⊗ₜ[F] (1 : E) := by simp [B, b, Algebra.TensorProduct.basis_apply]
    have hB1 : B 1 = (1 : Fv F v) ⊗ₜ[F] (θ : E) := by simp [B, b, Algebra.TensorProduct.basis_apply]
    intro y
    refine ⟨B.repr y 0, B.repr y 1, ?_⟩
    conv_lhs => rw [← B.sum_repr y]
    rw [Fin.sum_univ_two, hB0, hB1, smul_eq_sc, smul_eq_sc, ← Algebra.TensorProduct.one_def, mul_one]
    rfl
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : Fv F v, IsUnif v ϖ := ⟨unifV v, unifV_val v⟩
  obtain ⟨ρ, -, hρk, -⟩ := resQ_of σ J ψ v (thetaBas_of σ J ψ v (thetaSpan_holds σ J ψ v)) hstd hun ϖ hϖ
  have hϖ1 : Valued.v ϖ < 1 := by rw [show Valued.v ϖ = _ from hϖ]; decide
  have hnotPO : ∀ d0 d1 : Fv F v, (d0 = 1 ∨ d1 = 1) →
      sc (E := E) v d0 + sc (E := E) v d1 * iθ ∉ PO (E := E) v ϖ := by
    rintro d0 d1 hd ⟨o, ho, hzo⟩
    obtain ⟨e0, e1, he⟩ := hsp o ho
    have hz' : sc (E := E) v d0 + sc (E := E) v d1 * iθ =
        sc (E := E) v (ϖ * e0) + sc (E := E) v (ϖ * e1) * iθ := by
      rw [hzo, he]; simp only [sc_eq', map_mul]; ring
    have hsub := hind (d0 - ϖ * e0) (d1 - ϖ * e1) (by simp only [sc_eq', map_sub] at hz' ⊢; linear_combination hz')
    have key : ∀ (d : Fv F v) (e' : v.adicCompletionIntegers F), d - ϖ * e' = 0 → d = 1 → False := by
      intro d e' h0 h1
      subst h1
      have h' : (1 : Fv F v) = ϖ * e' := sub_eq_zero.1 h0
      have hv := congrArg Valued.v h'
      rw [map_one, map_mul] at hv
      have he1 : Valued.v (e' : Fv F v) ≤ 1 := e'.2
      have hlt : Valued.v ϖ * Valued.v (e' : Fv F v) < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' he1) hϖ1
      exact (ne_of_lt hlt).symm hv
    rcases hd with h | h
    · exact key d0 e0 hsub.1 h
    · exact key d1 e1 hsub.2 h
  have hmem : ∀ a : Fv F v, Valued.v a ≤ 1 → ∀ o ∈ OEv (E := E) v, sc (E := E) v a * o ∈ OEv (E := E) v :=
    fun a ha o ho => sc_mul_mem_oEv v ha ho
  have hnorm : ∀ y : Fv F v ⊗[F] E, y ≠ 0 → ∃ c : Fv F v,
      sc (E := E) v c * y ∈ OEv (E := E) v ∧ sc (E := E) v c * y ∉ PO (E := E) v ϖ := by
    intro y hy
    obtain ⟨c0, c1, rfl⟩ := hcoord y
    by_cases hle : Valued.v c1 ≤ Valued.v c0
    · have hc0 : c0 ≠ 0 := by
        rintro rfl
        have hc1 : c1 = 0 := by
          rw [map_zero, le_zero_iff, map_eq_zero] at hle; exact hle
        apply hy; rw [hc1]; simp [sc_eq']
      have e : sc (E := E) v c0⁻¹ * (sc (E := E) v c0 + sc (E := E) v c1 * iθ) =
          sc (E := E) v 1 + sc (E := E) v (c0⁻¹ * c1) * iθ := by
        simp only [mul_add, ← mul_assoc, ← scm, inv_mul_cancel₀ hc0]
      have hv : Valued.v (c0⁻¹ * c1) ≤ 1 :=
        calc Valued.v (c0⁻¹ * c1) = Valued.v c0⁻¹ * Valued.v c1 := map_mul _ _ _
          _ ≤ Valued.v c0⁻¹ * Valued.v c0 := mul_le_mul_of_nonneg_left hle zero_le'
          _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
      refine ⟨c0⁻¹, ?_, ?_⟩
      · rw [e]
        exact Orb.oev_add v (by simpa using hmem 1 (by rw [map_one]) 1 (Orb.oSub (E := E) v).1)
          (hmem _ hv _ (Orb.gen_mem v θ))
      · rw [e]; exact hnotPO 1 _ (Or.inl rfl)
    · push Not at hle
      have hc1 : c1 ≠ 0 := by
        rintro rfl
        rw [map_zero] at hle
        exact absurd hle (not_lt_of_ge zero_le')
      have e : sc (E := E) v c1⁻¹ * (sc (E := E) v c0 + sc (E := E) v c1 * iθ) =
          sc (E := E) v (c1⁻¹ * c0) + sc (E := E) v 1 * iθ := by
        simp only [mul_add, ← mul_assoc, ← scm, inv_mul_cancel₀ hc1]
      have hv : Valued.v (c1⁻¹ * c0) ≤ 1 :=
        calc Valued.v (c1⁻¹ * c0) = Valued.v c1⁻¹ * Valued.v c0 := map_mul _ _ _
          _ ≤ Valued.v c1⁻¹ * Valued.v c1 := mul_le_mul_of_nonneg_left hle.le zero_le'
          _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc1, map_one]
      refine ⟨c1⁻¹, ?_, ?_⟩
      · rw [e]
        exact Orb.oev_add v (by simpa using hmem _ hv 1 (Orb.oSub (E := E) v).1)
          (hmem 1 (by rw [map_one]) _ (Orb.gen_mem v θ))
      · rw [e]; exact hnotPO _ 1 (Or.inr rfl)
  by_contra hne
  push Not at hne
  obtain ⟨c, hc1, hc2⟩ := hnorm e hne.1
  obtain ⟨c', hc1', hc2'⟩ := hnorm (1 - e) (sub_ne_zero.2 (Ne.symm hne.2))
  haveI : IsDomain (QE (E := E) v) := (Ideal.Quotient.isDomain_iff_prime _).2 hp
  have h0 : (sc (E := E) v c * e) * (sc (E := E) v c' * (1 - e)) = 0 := by
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
    calc _ = sc (E := E) v c * sc (E := E) v c' * (e * (1 - e)) := by ring
      _ = 0 := by rw [h1, mul_zero]
  let z1 : OR (E := E) v := ⟨_, hc1⟩
  let z2 : OR (E := E) v := ⟨_, hc1'⟩
  have hz : z1 * z2 = 0 := Subtype.ext h0
  have h := congrArg ρ hz
  rw [map_mul, map_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact hc2 ((hρk z1).1 h)
  · exact hc2' ((hρk z2).1 h)

theorem resAlg_of_sp (hS : EtaSp σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_etaSp σ J ψ v (etaIn_holds σ J ψ v) hS

end PI.OmLocU.Red
