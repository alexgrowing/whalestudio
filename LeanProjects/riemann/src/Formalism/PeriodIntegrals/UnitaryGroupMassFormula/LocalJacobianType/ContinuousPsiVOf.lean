import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ContinuousTrESymm

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def piu : Fv F v := (PI.VolStabSW.exists_unif_Fv v).choose

theorem piu_ne : piu v ≠ 0 := (PI.VolStabSW.exists_unif_Fv v).choose_spec.1

theorem piu_tendsto : Tendsto (fun k : ℕ => piu v ^ k) atTop (𝓝 0) :=
  (PI.VolStabSW.exists_unif_Fv v).choose_spec.2.1

theorem piu_mem : piu v ∈ v.adicCompletionIntegers F :=
  (PI.VolStabSW.exists_unif_Fv v).choose_spec.2.2

theorem tube {X : Type} [AddCommGroup X] [Module (Fv F v) X] [TopologicalSpace X]
    [ContinuousSMul (Fv F v) X] {C : Set X} (hC : IsCompact C) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) : ∀ᶠ k : ℕ in atTop, ∀ c ∈ C, piu v ^ k • c ∈ U := by
  have hP : ∀ c ∈ C, ∀ᶠ z : Fv F v × X in 𝓝 ((0 : Fv F v), c), z.1 • z.2 ∈ U := by
    intro c _
    have hc : Continuous fun z : Fv F v × X => z.1 • z.2 := continuous_fst.smul continuous_snd
    exact (hc.tendsto ((0 : Fv F v), c)).eventually_mem (by simpa using hU)
  have hev := hC.eventually_forall_of_forall_eventually (P := fun s c => s • c ∈ U) hP
  exact (piu_tendsto v).eventually hev

variable (ψ : AddChar (AF F) ℂ)

theorem singleV_zero : singleV F v 0 = 0 := by
  have h := PI.VolStabSW.SdUniqW.singleV_add v (0 : Fv F v) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem psiV_zero : psiV F ψ v 0 = 1 := by
  simp only [psiV, singleV_zero]
  exact AddChar.map_zero_eq_one ψ

theorem psiV_add' (r s : Fv F v) : psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s :=
  PI.VolStabSW.SdUniqW.psiV_add ψ v r s

theorem psiV_neg_mul (r : Fv F v) : psiV F ψ v (-r) * psiV F ψ v r = 1 := by
  rw [← psiV_add', neg_add_cancel, psiV_zero]

theorem psiV_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    psiV F ψ v (∑ i ∈ s, f i) = ∏ i ∈ s, psiV F ψ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [psiV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, psiV_add', ih]

theorem psiV_nsmul (n : ℕ) (r : Fv F v) : psiV F ψ v (n • r) = psiV F ψ v r ^ n := by
  induction n with
  | zero => simp [psiV_zero]
  | succ n ih => rw [succ_nsmul, psiV_add', ih, pow_succ]

def OpenKer : Prop :=
  ∃ k : ℕ, ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1

def ballK (k : ℕ) : Set (Fv F v) := {t | (piu v ^ k)⁻¹ * t ∈ v.adicCompletionIntegers F}

theorem ballK_mem_nhds (k : ℕ) : ballK v k ∈ 𝓝 (0 : Fv F v) := by
  have ho : IsOpen (ballK v k) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)
  exact ho.mem_nhds (by simp [ballK, zero_mem])

theorem psiV_ballK {k : ℕ} (hk : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (piu v ^ k * c) = 1)
    {t : Fv F v} (ht : t ∈ ballK v k) : psiV F ψ v t = 1 := by
  have h := hk _ ht
  rwa [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (piu_ne v)), one_mul] at h

theorem continuous_psiV_of (h : OpenKer v ψ) : Continuous (psiV F ψ v) := by
  obtain ⟨k, hk⟩ := h
  refine continuous_iff_continuousAt.2 fun r => ?_
  have hev : ∀ᶠ t in 𝓝 r, psiV F ψ v t = psiV F ψ v r := by
    have h1 : Tendsto (fun t => t - r) (𝓝 r) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [h1 (ballK_mem_nhds v k)] with t ht
    have := psiV_add' v ψ r (t - r)
    rw [add_sub_cancel, psiV_ballK v ψ hk ht, mul_one] at this
    exact this
  exact continuousAt_const.congr (hev.mono fun t ht => ht.symm)

theorem norm_psiV_of (h : OpenKer v ψ) (r : Fv F v) : ‖psiV F ψ v r‖ = 1 := by
  have hc := continuous_psiV_of v ψ h

  have hbd : ∀ x : Fv F v, ∃ B : ℝ, ∀ n : ℕ, ‖psiV F ψ v x‖ ^ n ≤ B := by
    intro x
    obtain ⟨j, hj⟩ := ((piu_tendsto v).mul_const x).eventually
      ((Valued.isOpen_valuationSubring (Fv F v)).mem_nhds (by simp [zero_mem]) :
        ((v.adicCompletionIntegers F : Set (Fv F v))) ∈ 𝓝 (0 * x)) |>.exists
    set H : Set (Fv F v) := {t | piu v ^ j * t ∈ v.adicCompletionIntegers F}
    have hHc : IsCompact H := by
      have e : H = (fun t => (piu v ^ j)⁻¹ * t) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
        ext t
        constructor
        · intro ht
          refine ⟨piu v ^ j * t, ht, ?_⟩
          simp [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j (piu_ne v))]
        · rintro ⟨s, hs, rfl⟩
          simpa [H, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (piu_ne v))] using hs
      rw [e]
      exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
    obtain ⟨B, hB⟩ := hHc.exists_bound_of_continuousOn (hc.norm.continuousOn)
    refine ⟨B, fun n => ?_⟩
    have hn : (n • x) ∈ H := by
      show piu v ^ j * (n • x) ∈ v.adicCompletionIntegers F
      rw [mul_smul_comm]
      exact (v.adicCompletionIntegers F).toAddSubgroup.nsmul_mem hj n
    have h2 := hB _ hn
    rw [psiV_nsmul, norm_norm, norm_pow] at h2
    exact h2
  have hle : ∀ x : Fv F v, ‖psiV F ψ v x‖ ≤ 1 := by
    intro x
    obtain ⟨B, hB⟩ := hbd x
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    exact absurd (hB n) (not_le.2 hn)
  have h1 := hle r
  have h2 := hle (-r)
  have h3 : ‖psiV F ψ v (-r)‖ * ‖psiV F ψ v r‖ = 1 := by rw [← norm_mul, psiV_neg_mul, norm_one]
  nlinarith [norm_nonneg (psiV F ψ v r), norm_nonneg (psiV F ψ v (-r))]

theorem openKer_of (t : Fv F v) (ht : t ≠ 0)
    (h : ∀ c ∈ v.adicCompletionIntegers F, psiV F ψ v (c * t) = 1) : OpenKer v ψ := by
  have hU : {s : Fv F v | t⁻¹ * s ∈ v.adicCompletionIntegers F} ∈ 𝓝 (0 : Fv F v) :=
    ((Valued.isOpen_valuationSubring _).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [zero_mem])
  obtain ⟨k, hk⟩ := (tube v (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v) hU).exists
  refine ⟨k, fun c hc => ?_⟩
  have h1 := h _ (hk c hc)
  simp only [smul_eq_mul] at h1
  have e : t⁻¹ * (piu v ^ k * c) * t = piu v ^ k * c := by field_simp
  rwa [e] at h1

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
