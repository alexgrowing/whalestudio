import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OkPt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ γ, IsPtRep X u u' w γ) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

def ooF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ x : X.B.I.Ginf) : X.Vpi u' →L[ℂ] X.Vpi u :=
  TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))

def StInv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ s ∈ StInf X u u' (gamW X u u' w), ∀ x,
    ooF X u u' (gamW X u u' w) (s * x) = ooF X u u' (gamW X u u' w) x

def StBruhat (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∃ b : X.B.I.Ginf → ℝ≥0∞, Measurable b ∧ ∀ x, ∫⁻ s, b (s * x) ∂μR = 1

def LocWeil (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, SigmaFinite (ν v)) ∧ Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (Measure.pi ν)

section Uniq

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem lint_eq_bruhat (μR ν : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (hν : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν) (f : X.B.I.Ginf → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ s ∈ S, ∀ x, f (s * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, b x * f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
  rw [hν (fun x => b x * f x) (hbm.mul hf)]
  refine lintegral_congr fun x => ?_
  show f x = ∫⁻ s, b (s * x) * f (s * x) ∂μR
  have hS : ∀ᵐ s ∂μR, s ∈ S := by
    rw [ae_iff]
    exact hS0
  have h1 : ∫⁻ s, b (s * x) * f (s * x) ∂μR = ∫⁻ s, b (s * x) * f x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with s hs
    rw [hinv s hs x]
  rw [h1, show ∫⁻ s, b (s * x) * f x ∂μR = (∫⁻ s, b (s * x) ∂μR) * f x from
    lintegral_mul_const _ (hbm.comp (measurable_mul_const x)), hb1, one_mul]

@[instance_reducible] def invMS (S : Set X.B.I.Ginf) : MeasurableSpace X.B.I.Ginf where
  MeasurableSet' A := MeasurableSet A ∧ ∀ s ∈ S, ∀ x, (s * x ∈ A ↔ x ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun s hs x => not_congr (hA.2 s hs x)⟩
  measurableSet_iUnion A hA := ⟨MeasurableSet.iUnion fun i => (hA i).1, fun s hs x => by
    simp only [Set.mem_iUnion]; exact exists_congr fun i => (hA i).2 s hs x⟩

theorem invMS_le (S : Set X.B.I.Ginf) : invMS S ≤ (inferInstance : MeasurableSpace X.B.I.Ginf) := by
  exact fun _ hA => hA.1

theorem integral_eq_of_quot (μR ν₁ ν₂ : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (h₁ : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν₁) (h₂ : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν₂)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (F : X.B.I.Ginf → E) (hF : Continuous F) (hinv : ∀ s ∈ S, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν₁ = ∫ x, F x ∂ν₂ := by
  have hle := invMS_le (X := X) S
  have hmeas : ∀ A, MeasurableSet[invMS S] A → ν₁ A = ν₂ A := by
    intro A hA
    have hAm : MeasurableSet A := hA.1
    have hind : ∀ s ∈ S, ∀ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (s * x) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro s hs x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hA.2 s hs x).2 hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (fun hx' => hx ((hA.2 s hs x).1 hx'))]
    have e₁ := lint_eq_bruhat μR ν₁ S hS0 b hbm hb1 h₁ _ (measurable_const.indicator hAm) hind
    have e₂ := lint_eq_bruhat μR ν₂ S hS0 b hbm hb1 h₂ _ (measurable_const.indicator hAm) hind
    rw [lintegral_indicator_const hAm, one_mul] at e₁ e₂
    rw [e₁, e₂]
  have htrim : ν₁.trim hle = ν₂.trim hle := by
    refine @Measure.ext _ (invMS S) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA]
    exact hmeas A hA
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  borelize E
  have hFm : StronglyMeasurable[invMS S] F := by
    have hFm' : Measurable[invMS S] F := by
      intro B hB
      refine ⟨hF.measurable hB, fun s hs x => ?_⟩
      simp only [Set.mem_preimage, hinv s hs x]
    exact hFm'.stronglyMeasurable
  rw [integral_trim (μ := ν₁) hle hFm, integral_trim (μ := ν₂) hle hFm, htrim]

end Uniq

private theorem norm_tensU_eq_prod_norm (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (x : ∀ v, X.Vloc u v) : ‖X.tensU u x‖ = ∏ v, ‖x v‖ := by
  have h2 := X.tensU_inner u x x
  simp only [inner_self_eq_norm_sq_to_K] at h2
  rw [Finset.prod_pow] at h2
  have h3 : ‖X.tensU u x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _) two_ne_zero).1 h3

private theorem norm_rk1_eq_mul_norm {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (a : V) (b : V') :
    ‖TermOp.rk1 a b‖ = ‖b‖ * ‖a‖ := by
  unfold TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

private theorem eq_of_inner_tensU_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (a b : X.Vpi u) (hab : ∀ z, inner ℂ (X.tensU u z) a = inner ℂ (X.tensU u z) b) : a = b := by
  have hsub : ∀ c ∈ Submodule.span ℂ (Set.range (X.tensU u)), inner ℂ c (a - b) = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h0 := hsub (a - b) (by rw [X.tensU_span u]; trivial)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem tensU_eq_zero_of_apply_eq_zero (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (x : ∀ v, X.Vloc u v) (v0 : InfinitePlace X.B.I.F) (h : x v0 = 0) : X.tensU u x = 0 := by
  rw [← norm_eq_zero, norm_tensU_eq_prod_norm]
  exact Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [h, norm_zero])

theorem oo_eq_tens (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (μR νq : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (hσ : ∀ v, SigmaFinite (ν v))
    (hq : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR νq)
    (hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (Measure.pi ν))
    (hinv : ∀ s ∈ S, ∀ x, ooF X u u' γ (s * x) = ooF X u u' γ x) (y : ∀ v, X.Vloc u' v) :
    (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
      Formalism.L2.SG.TermOp.OO νq Set.univ (X.Wu u) (X.Wu u') γ) (X.tensU u' y) =
    X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
      Jv (ν v) (X.Wloc u v) (X.Wloc u' v) (γ v)) (y v)) := by
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ _
  have hWc : ∀ u₀, Continuous (X.Wu u₀) := fun u₀ => (X.Wu_spec u₀).2.2.1
  have hcont : Continuous (ooF X u u' γ) := by
    unfold ooF
    refine continuous_clm_apply.2 fun ξ => ?_
    simp only [TermOp.rankOneInnerOperator_apply]
    exact (((hWc u').comp (continuous_const.mul continuous_id)).inner continuous_const).smul (hWc u)
  have hOO : Formalism.L2.SG.TermOp.OO νq Set.univ (X.Wu u) (X.Wu u') γ =
      Formalism.L2.SG.TermOp.OO (Measure.pi ν) Set.univ (X.Wu u) (X.Wu u') γ := by
    unfold Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ, Measure.restrict_univ]
    exact integral_eq_of_quot μR νq (Measure.pi ν) S hS0 b hbm hb1 hq hp (ooF X u u' γ) hcont hinv
  rw [hOO]
  have hJ : ∀ v, Jv (ν v) (X.Wloc u v) (X.Wloc u' v) (γ v) =
      ∫ t, TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) ∂(ν v) := by
    intro v
    simp only [Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ]
  simp only [hJ, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ]
  have hLc : ∀ v, Continuous fun t : Formalism.REAL.UJ (X.B.I.ε v) =>
      TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) := by
    intro v
    refine continuous_clm_apply.2 fun ξ => ?_
    simp only [TermOp.rankOneInnerOperator_apply]
    exact (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).inner
      continuous_const).smul (X.Wloc_cont u v)
  have hnormf : ∀ x : X.B.I.Ginf, ‖TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))‖ =
      ∏ v, ‖TermOp.rk1 (X.Wloc u v (x v)) (X.Wloc u' v ((γ v)⁻¹ * x v))‖ := by
    intro x
    simp only [norm_rk1_eq_mul_norm, X.Wu_tens, norm_tensU_eq_prod_norm, Pi.mul_apply, Pi.inv_apply,
      Finset.prod_mul_distrib]
  have hmeasf : AEStronglyMeasurable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
      (Measure.pi ν) := hcont.aestronglyMeasurable
  apply eq_of_inner_tensU_eq X u
  intro z
  by_cases hint : ∀ v, Integrable (fun t : Formalism.REAL.UJ (X.B.I.ε v) =>
      TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t))) (ν v)
  · have hfint : Integrable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
        (Measure.pi ν) :=
      Integrable.mono' (Integrable.fintype_prod_dep fun v => (hint v).norm) hmeasf
        (Filter.Eventually.of_forall fun x => (hnormf x).le)
    have hpt : ∀ x : X.B.I.Ginf,
        inner ℂ (X.tensU u z) (TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) (X.tensU u' y)) =
          ∏ v, inner ℂ (z v) (TermOp.rk1 (X.Wloc u v (x v)) (X.Wloc u' v ((γ v)⁻¹ * x v)) (y v)) := by
      intro x
      simp only [TermOp.rankOneInnerOperator_apply, X.Wu_tens, inner_smul_right, X.tensU_inner, Pi.mul_apply,
        Pi.inv_apply, Finset.prod_mul_distrib]
    rw [ContinuousLinearMap.integral_apply hfint, ← integral_inner (hfint.apply_continuousLinearMap _),
      X.tensU_inner]
    simp_rw [hpt]
    rw [integral_fintype_prod_eq_prod (fun v t =>
      inner ℂ (z v) (TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) (y v)))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ContinuousLinearMap.integral_apply (hint v),
      ← integral_inner ((hint v).apply_continuousLinearMap _)]
  · push Not at hint
    obtain ⟨v0, hv0⟩ := hint
    have hR0 : X.tensU u (fun v => (∫ t, TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) ∂(ν v))
        (y v)) = 0 := by
      apply tensU_eq_zero_of_apply_eq_zero X u _ v0
      simp only [integral_undef hv0, ContinuousLinearMap.zero_apply]
    have hL0 : (∫ x, TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) ∂(Measure.pi ν)) (X.tensU u' y) = 0 := by
      by_cases hf : Integrable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
          (Measure.pi ν)
      · have h0 : ∫ x, ‖TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))‖ ∂(Measure.pi ν) = 0 := by
          simp_rw [hnormf]
          rw [integral_fintype_prod_eq_prod (fun v t =>
            ‖TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t))‖)]
          exact Finset.prod_eq_zero (Finset.mem_univ v0)
            (integral_undef fun hh => hv0 ((integrable_norm_iff
              (hLc v0).aestronglyMeasurable).1 hh))
        have hae := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) hf.norm).1 h0
        have hae' : (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))) =ᵐ[Measure.pi ν] 0 := by
          filter_upwards [hae] with x hx
          simpa using hx
        rw [integral_congr_ae hae']
        simp
      · rw [integral_undef hf, ContinuousLinearMap.zero_apply]
    rw [hL0, hR0]

def psiU (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : ℂ :=
  Formalism.L2.SG.HidaSetting.psiInf X.B.I X.B.g X.eR X.fR (X.zR u) s

def StRel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ s ∈ StInf X u u' (gamW X u u' w),
    psiU X u s * star (psiU X u' ((gamW X u u' w)⁻¹ * s * gamW X u u' w)) = 1

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (c d : ℂ) (a : V) (b : V') :
    TermOp.rk1 (c • a) (d • b) = (c * star d) • TermOp.rk1 a b := by
  ext x
  simp only [TermOp.rk1, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
    innerSL_apply_apply, inner_smul_left]
  congr 1
  rw [Complex.star_def]
  ring

theorem stInv_of_rel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (h : StRel X u u') : StInv X u u' := by
  intro w hw s hs x
  have hrel := h w hw s hs
  have hW : ∀ (u₀ : D.what₂.Word) (t : X.B.I.Ginf), t ∈ X.NinfU u₀ → ∀ y,
      X.Wu u₀ (t * y) = psiU X u₀ t • X.Wu u₀ y := by
    intro u₀ t ht y
    have h1 := (X.Wu_spec u₀).1 t (fun v => (ht v).1) y
    rw [(X.piU_rep u₀).2.2.2.1 t ht] at h1
    simp only [ContinuousLinearMap.one_apply] at h1
    exact h1
  unfold ooF
  rw [hW u s hs.1 x,
    show (gamW X u u' w)⁻¹ * (s * x) = ((gamW X u u' w)⁻¹ * s * gamW X u u' w) * ((gamW X u u' w)⁻¹ * x) by
      group,
    hW u' _ hs.2, rankOneInnerOperator_smul_smul_eq_mul_conj_smul, hrel, one_smul]

end Formalism.L2.SG.Pf.Carrier.JointQuot
