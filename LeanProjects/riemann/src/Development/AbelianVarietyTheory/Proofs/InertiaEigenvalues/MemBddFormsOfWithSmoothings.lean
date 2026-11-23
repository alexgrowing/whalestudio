import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.Petersson

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def bddForms (ω : HChar E) : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | Continuous φ ∧ (∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
    (∀ (z : Ideles E) g, φ (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g) ∧ ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, C, h4⟩ ⟨k1, k2, k3, D, k4⟩
    exact ⟨h1.add k1, fun γ g => by simp only [Pi.add_apply, h2, k2], fun z g => by simp only [Pi.add_apply, h3, k3, mul_add],
      C + D, fun g => (norm_add_le _ _).trans (add_le_add (h4 g) (k4 g))⟩
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => (mul_zero _).symm, 0, fun _ => norm_zero.le⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, C, h4⟩
    exact ⟨h1.const_smul c, fun γ g => by simp only [Pi.smul_apply, h2],
      fun z g => by simp only [Pi.smul_apply, h3, smul_eq_mul]; ring,
      ‖c‖ * C, fun g => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (h4 g) (norm_nonneg _))⟩

variable {ω : HChar E} {φ ψ F : GA E a → ℂ}

theorem mem_bddForms_of_cuspSub (hB : GlobalTheory.Published.CuspFormsBoundedGL) (hω : ω.IsUnitary) {π : CuspSub E a}
    (h : π.HasCentChar ω) {φ : Sm E a} (hφ : φ ∈ π.V) : φ.1 ∈ bddForms E a ω :=
  have hc := CuspSub.hasCentral_iff.2 h
  ⟨ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level, (π.cusp φ hφ).1.left, hc.apply hφ,
    hB.of_isUnitary ⟨ω, hω, hc⟩ hφ⟩

theorem mul_right_mem_bddForms (h : φ ∈ bddForms E a ω) (k : GA E a) : (fun g => φ (g * k)) ∈ bddForms E a ω :=
  ⟨h.1.comp (continuous_mul_const k), fun γ g => by simp only [mul_assoc, h.2.1],
    fun z g => by simp only [mul_assoc, h.2.2.1], h.2.2.2.imp fun _ hC _ => hC _⟩

theorem mul_conj_scalar (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) (z : Ideles E) (g : GA E a) :
    φ (GeneralLinearGroup.scalar (Fin a) z * g) * conj (ψ (GeneralLinearGroup.scalar (Fin a) z * g)) = φ g * conj (ψ g) := by
  rw [h.2.2.1, h'.2.2.1, map_mul, mul_mul_mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hω z]
  simp

theorem mul_conj_splitCentre (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) (t : ℝ) (g : GA E a) :
    φ (splitCentre E a t * g) * conj (ψ (splitCentre E a t * g)) = φ g * conj (ψ g) := by
  rw [splitCentre_eq_scalar]; exact mul_conj_scalar hω h h' _ g

theorem leftInv_mul_conj (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    LeftInv (latticeGL E a) fun g => φ g * conj (ψ g) :=
  leftInv_latticeGL (fun γ g => by simp only [h.2.1, h'.2.1]) (mul_conj_splitCentre hω h h')

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem aesm_descend (hF : LeftInv (latticeGL E a) F) (hc : Continuous F) :
    AEStronglyMeasurable (descend (latticeGL E a) F) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) :=
  aestronglyMeasurable_quotMeasure_iff_lift.2 (by rw [hF.lift_descend]; exact hc.aestronglyMeasurable)

theorem aesm_mul_conj (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    AEStronglyMeasurable (fun q => descend (latticeGL E a) φ q * conj (descend (latticeGL E a) ψ q))
      (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) :=
  aesm_descend μ (leftInv_mul_conj hω h h') (h.1.mul (Complex.continuous_conj.comp h'.1))

theorem integrable_mul_conj (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    Integrable (fun q => descend (latticeGL E a) φ q * conj (descend (latticeGL E a) ψ q))
      (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD⟩ := h'.2.2.2
  refine Integrable.of_bound (aesm_mul_conj μ hω h h') (C * D) (Eventually.of_forall fun q => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

variable {μ} in

theorem pet_eq_setIntegral (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) :
    IntegrableOn (fun g => φ g * conj (ψ g)) 𝓕 μ ∧ pet (latticeGL E a) μ φ ψ = ∫ g in 𝓕, φ g * conj (ψ g) ∂μ := by
  have hI := leftInv_mul_conj hω h h'
  constructor
  · have := ((measurePreserving_mk h𝓕).integrable_comp (aesm_mul_conj μ hω h h')).2 (integrable_mul_conj μ hω h h')
    exact this.congr (Eventually.of_forall hI.descend_mk)
  · exact (integral_quotMeasure h𝓕 _).trans (integral_congr_ae (Eventually.of_forall hI.descend_mk))

theorem memL2_norm_bounded_form (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) : MemL2Quotient (latticeGL E a) μ fun g => (‖φ g‖ : ℂ) := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hI : LeftInv (latticeGL E a) fun g => (‖φ g‖ : ℂ) := leftInv_latticeGL (fun γ g => by simp only [h.2.1])
    fun t g => by simp only [splitCentre_eq_scalar, h.2.2.1, norm_mul, hω _, one_mul]
  obtain ⟨C, hC⟩ := h.2.2.2
  exact ⟨hI, MemLp.of_bound (aesm_descend μ hI (Complex.continuous_ofReal.comp h.1.norm)) C
    (Eventually.of_forall fun q => by simpa [descend] using hC _)⟩

theorem conj_pet (φ ψ : GA E a → ℂ) : conj (pet (latticeGL E a) μ φ ψ) = pet (latticeGL E a) μ ψ φ := by
  rw [pet, pet, ← integral_conj]
  simp [mul_comm]

theorem pet_add_left (hω : ω.IsUnitary) {φ' : GA E a → ℂ} (h : φ ∈ bddForms E a ω) (h1 : φ' ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (φ + φ') ψ = pet (latticeGL E a) μ φ ψ + pet (latticeGL E a) μ φ' ψ := by
  rw [pet, pet, pet, ← integral_add (integrable_mul_conj μ hω h h') (integrable_mul_conj μ hω h1 h')]
  simp only [descend, Pi.add_apply, add_mul]

theorem pet_smul_left (c : ℂ) (φ ψ : GA E a → ℂ) :
    pet (latticeGL E a) μ (c • φ) ψ = c * pet (latticeGL E a) μ φ ψ := by
  rw [pet, pet, ← integral_const_mul]
  simp only [descend, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem pet_self_pos (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h0 : φ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ pet (latticeGL E a) μ φ φ = r := by
  have hm := memL2_norm_bounded_form μ hω h
  have hn := toL2_ne_zero hm (Complex.continuous_ofReal.comp h.1.norm) fun e => h0 (funext fun g => by
    simpa using congrFun e g)
  refine ⟨‖hm.toL2‖ ^ 2, by positivity, ?_⟩
  have e := hm.inner_toL2_eq_theta_pairing hm
  rw [inner_self_eq_norm_sq_to_K] at e
  have e2 : pet (latticeGL E a) μ φ φ = pet (latticeGL E a) μ (fun g => (‖φ g‖ : ℂ)) fun g => (‖φ g‖ : ℂ) := by
    simp only [pet, descend, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_real, norm_norm]
  rw [e2, ← e]
  simp

theorem pet_mul_right (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) (k : GA E a) :
    pet (latticeGL E a) μ (fun g => φ (g * k)) (fun g => ψ (g * k)) = pet (latticeGL E a) μ φ ψ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hI := leftInv_mul_conj hω h h'
  have hp := measurePreserving_rmul (Γ := latticeGL E a) (μ := μ) k
  have e := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ aesm_mul_conj μ hω h h')
  rw [hp.map_eq] at e
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun q => ?_)) e.symm
  exact Quotient.inductionOn q fun x => ((hI.mul_right k).descend_mk x).trans (hI.descend_mk (x * k)).symm

theorem pet_mul_right_left (hω : ω.IsUnitary) (h : φ ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) (k : GA E a) :
    pet (latticeGL E a) μ (fun g => φ (g * k)) ψ = pet (latticeGL E a) μ φ fun g => ψ (g * k⁻¹) := by
  rw [← pet_mul_right μ hω h (mul_right_mem_bddForms h' k⁻¹) k]
  simp only [mul_inv_cancel_right]

theorem pet_lie (hω : ω.IsUnitary) (X : Lie E a) {φ ψ : Sm E a} (h : φ.1 ∈ bddForms E a ω) (h' : ψ.1 ∈ bddForms E a ω)
    (hX : (lie E a X φ).1 ∈ bddForms E a ω) (hX' : (lie E a X ψ).1 ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (lie E a X φ).1 ψ.1 = -pet (latticeGL E a) μ φ.1 (lie E a X ψ).1 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD⟩ := h'.2.2.2
  obtain ⟨C', hC'⟩ := hX.2.2.2
  obtain ⟨D', hD'⟩ := hX'.2.2.2
  set e : ℝ → GA E a := fun t => infGL E a (GlobalTheory.ExpDeriv.expGL X t) with he
  have e0 : e 0 = 1 := by simp [he, GlobalTheory.ExpDeriv.expGL_zero]
  have hi := (integrable_mul_conj μ hω hX h').add (integrable_mul_conj μ hω h hX')
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) (x₀ := (0 : ℝ))
    (F := fun t q => φ.1 (q.out * e t) * conj (ψ.1 (q.out * e t)))
    (F' := fun t q => (lie E a X φ).1 (q.out * e t) * conj (ψ.1 (q.out * e t)) +
      φ.1 (q.out * e t) * conj ((lie E a X ψ).1 (q.out * e t)))
    (bound := fun _ => C' * D + C * D') (s := Set.univ) univ_mem
    (Eventually.of_forall fun t => aesm_mul_conj μ hω (mul_right_mem_bddForms h (e t)) (mul_right_mem_bddForms h' (e t)))
    (integrable_mul_conj μ hω (mul_right_mem_bddForms h (e 0)) (mul_right_mem_bddForms h' (e 0)))
    (by simp only [e0, mul_one]; exact hi.1)
    (Eventually.of_forall fun q t _ => (norm_add_le _ _).trans (by
      simp only [norm_mul, Complex.norm_conj]
      exact add_le_add (mul_le_mul (hC' _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC' 1)))
        (mul_le_mul (hC _) (hD' _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1)))))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (GlobalTheory.ExpDeriv.hasDerivAt_along X φ q.out t).mul
      (GlobalTheory.ExpDeriv.hasDerivAt_along X ψ q.out t).star)).2
  have hc : (fun t => ∫ q, φ.1 (q.out * e t) * conj (ψ.1 (q.out * e t)) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) =
      fun _ => pet (latticeGL E a) μ φ.1 ψ.1 := funext fun t => pet_mul_right μ hω h h' (e t)
  rw [hc] at key
  have k2 := key.unique (hasDerivAt_const _ _)
  simp only [e0, mul_one] at k2
  rw [eq_neg_iff_add_eq_zero, pet, pet,
    ← integral_add (integrable_mul_conj μ hω hX h') (integrable_mul_conj μ hω h hX')]
  exact k2

section Smoothing

open GlobalTheory.CuspQuot GlobalTheory.AutGrowth

theorem chart_mem_bddForms (h : φ ∈ bddForms E a ω) (x : Lie E a) : (fun g => chart φ g x) ∈ bddForms E a ω := by
  unfold chart
  split_ifs
  · exact mul_right_mem_bddForms h _
  · exact zero_mem _

variable (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α β : Lie E a → ℂ}

theorem smoothing_mem_bddForms (hα : IsTest (invSet E a) α) (h : φ ∈ bddForms E a ω) :
    smoothing ν α φ ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hαi : Integrable α ν := hα.1.continuous.integrable_of_hasCompactSupport hα.2.1
  refine ⟨continuous_smoothing ν hα h.1 hC, fun γ g => ?_, fun z g => ?_, ∫ y, ‖α y‖ * C ∂ν, fun g =>
    norm_integral_le_of_norm_le (hαi.norm.mul_const C) (.of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC g y) (norm_nonneg _)))⟩
  · exact integral_congr_ae (.of_forall fun y => congrArg (α y * ·) ((chart_mem_bddForms h y).2.1 γ g))
  · refine Eq.trans (integral_congr_ae (.of_forall fun y => ?_)) (integral_const_mul _ _)
    exact (congrArg (α y * ·) ((chart_mem_bddForms h y).2.2.1 z g)).trans (mul_left_comm _ _ _)

theorem pet_smoothing_left (hω : ω.IsUnitary) (hα : IsTest (invSet E a) α) (h : φ ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (smoothing ν α φ) ψ = ∫ x, α x * pet (latticeGL E a) μ (fun g => chart φ g x) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hαi : Integrable α ν := hα.1.continuous.integrable_of_hasCompactSupport hα.2.1
  have hi : Integrable (fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine (((integrable_const (C * D)).mul_prod hαi.norm)).mono'
      ((continuous_integrand hα h.1).mul (Complex.continuous_conj.comp (h'.1.comp continuous_fst))).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (norm_chart_le hC _ _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (smoothing_mem_bddForms ν hα h) h' hD).2]
  simp only [smoothing, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (chart_mem_bddForms h x) h' hD).2, ← integral_const_mul, mul_assoc]

omit [IsTotallyComplex E] in

def invL (x : Lie E a) : Lie E a := toL (Matrix.of x)⁻¹

def starTest (α : Lie E a → ℂ) (y : Lie E a) : ℂ := conj (α (invL y)) * (|(fderiv ℝ invL y).det| : ℝ)

omit [IsTotallyComplex E] in
theorem invL_val (u : GL (Fin a) (Cinf E)) : invL (toL u.val) = toL (u⁻¹).val := (Matrix.coe_units_inv u).symm

omit [IsTotallyComplex E] in
theorem contDiffAt_invL {x : Lie E a} (h : x ∈ invSet E a) : ContDiffAt ℝ (⊤ : ℕ∞) invL x := by
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  have e : (invL : Lie E a → Lie E a) = fun x => T (Ring.inverse (S x)) :=
    funext fun x => Matrix.nonsing_inv_eq_ringInverse _
  obtain ⟨u, hu⟩ := h
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse (S x) := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := (⊤ : ℕ∞)) u
    rwa [hu] at this
  rw [e]
  exact T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)

def withSmoothings (π : CuspSub E a) : Submodule ℂ (Sm E a) :=
  π.V ⊔ Submodule.span ℂ {F | ∃ (f : Lie E a → ℂ) (φ : Sm E a), IsTest (invSet E a) f ∧ φ ∈ π.V ∧
    F.1 = GlobalTheory.JSW.smoothInf f φ.1}

theorem isTest_of_isTestInf (h : GlobalTheory.JSW.IsTestInf α) : IsTest (invSet E a) α :=
  ⟨h.1.of_le (by first | exact le_rfl | exact le_top), h.2⟩

theorem le_withSmoothings (π : CuspSub E a) : π.V ≤ withSmoothings π := le_sup_left

theorem lie_mem_withSmoothings {π : CuspSub E a} (X : Lie E a) {φ : Sm E a} (h : φ ∈ withSmoothings π) :
    lie E a X φ ∈ withSmoothings π := by
  refine (sup_le (fun ψ hψ => le_withSmoothings π (π.stable (.lie X) ψ hψ)) (Submodule.span_le.2 ?_) :
    withSmoothings π ≤ (withSmoothings π).comap (lie E a X)) h
  rintro F ⟨f, ψ, hf, hψ, e⟩
  refine Submodule.mem_sup_right (Submodule.subset_span ⟨dens X f, ψ, isTest_dens X hf, hψ, funext fun g => ?_⟩)
  rw [CuspRep.lie_apply, e]
  exact lieD_smoothing volume hf ψ.2 X g

theorem mem_bddForms_of_withSmoothings (hB : GlobalTheory.Published.CuspFormsBoundedGL) (hω : ω.IsUnitary) {π : CuspSub E a}
    (h : π.HasCentChar ω) {φ : Sm E a} (hφ : φ ∈ withSmoothings π) : φ.1 ∈ bddForms E a ω := by
  refine (sup_le (fun ψ hψ => mem_bddForms_of_cuspSub hB hω h hψ) (Submodule.span_le.2 ?_) :
    withSmoothings π ≤ (bddForms E a ω).comap (Sm E a).subtype) hφ
  rintro F ⟨f, ψ, hf, hψ, e⟩
  change F.1 ∈ bddForms E a ω
  rw [e]
  exact smoothing_mem_bddForms volume hf (mem_bddForms_of_cuspSub hB hω h hψ)

end Smoothing

end GlobalTheory.Petersson
