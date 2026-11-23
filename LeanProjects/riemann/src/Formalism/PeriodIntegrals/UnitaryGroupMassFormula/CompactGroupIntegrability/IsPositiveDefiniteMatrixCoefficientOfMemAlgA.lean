import Mathlib
import Formalism.PeriodIntegrals.WeylForU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.InstCompactUG

noncomputable section

namespace PI.UnitaryGroupMassFormula.PolyCoef

open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

lemma Jm_allPos (N : ℕ) : Jm (allPos N) = 1 := by
  simp [Jm, allPos]

lemma mem_Kset_iff {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) :
    g ∈ Kset (allPos N) ↔ g ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  simp [Kset, Jm_allPos]

lemma memK {N : ℕ} (g : UG N) : (g : Matrix (Fin N) (Fin N) ℂ) ∈ Kset (allPos N) :=
  (mem_Kset_iff _).mpr g.2

abbrev muU (N : ℕ) : Measure (UG N) := Measure.haar

section

variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}

def orb (hst : IsKStableOn (allPos N) σ S) (u : S) : UG N → S :=
  fun x => ⟨σ x u, hst _ (memK x) _ u.2⟩

lemma orb_cont (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S) (u : S) :
    Continuous (orb hst u) := by
  refine Continuous.subtype_mk ?_ _
  exact (hrep.2.2 (u : H)).comp_continuous continuous_subtype_val fun x => memK x

lemma integrable_cont {E : Type*} [NormedAddCommGroup E] {F : UG N → E} (hF : Continuous F) :
    Integrable F (muU N) :=
  hF.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

def T (hst : IsKStableOn (allPos N) σ S) (f : C(UG N, ℂ)) (u : S) : S :=
  ∫ x, f x • orb hst u x ∂(muU N)

lemma inner_sigma_T_eq_integral_mul_inner [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    (f : C(UG N, ℂ)) (u : S) (w : H) (h : UG N) :
    ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ =
      ∫ x, f x * ⟪w, σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) u⟫_ℂ ∂(muU N) := by
  have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
    integrable_cont (f.continuous.smul (orb_cont hrep hst u))
  unfold T
  have hL := ((innerSL ℂ w).comp ((σ (h : Matrix (Fin N) (Fin N) ℂ)).comp S.subtypeL)).integral_comp_comm hint
  refine hL.symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hmul : σ ((h * x : UG N) : Matrix (Fin N) (Fin N) ℂ) = (σ h).comp (σ x) :=
    hrep.1.2 _ (memK h) _ (memK x)
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, Submodule.subtypeL_apply, orb,
    Submodule.coe_smul, map_smul, inner_smul_right, hmul, smul_eq_mul]
  try rfl

lemma isPositiveDefinite_matrix_coefficient_of_mem_algA [FiniteDimensional ℂ S] (hrep : IsURepOn (Kset (allPos N)) σ) (hst : IsKStableOn (allPos N) σ S)
    {f : C(UG N, ℂ)} (hf : f ∈ algA N) (u : S) (w : H) :
    IsPD (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) := by
  obtain ⟨ι, _, a, b, ha, hb, hab⟩ := sep_of_mem hf
  have hcont : Continuous (fun y : UG N => ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) :=
    continuous_const.inner (continuous_subtype_val.comp (orb_cont hrep hst u))
  have hfun : ∀ h : UG N, ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ = ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := by
    intro h
    rw [inner_sigma_T_eq_integral_mul_inner hrep hst f u w h]
    have hsh := integral_mul_left_eq_self (μ := muU N)
      (fun y => f (h⁻¹ * y) * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ) h
    simp only [inv_mul_cancel_left] at hsh
    rw [hsh]
    simp_rw [hab h, Finset.sum_mul]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    · intro i _
      exact integrable_cont ((continuous_const.mul (hb i)).mul hcont)
  have e : (fun h : UG N => ⟪w, σ h ((T hst f u : S) : H)⟫_ℂ) = fun h => ∑ i, a i h *
      ∫ y, b i y * ⟪w, σ (y : Matrix (Fin N) (Fin N) ℂ) (u : H)⟫_ℂ ∂(muU N) := funext hfun
  rw [e]
  exact IsPD.sum _ fun i _ => (ha i).mul (IsPD.const _)

variable (σ S) in

def Ugood : Submodule ℂ S where
  carrier := {u | ∀ w : H, IsPD (fun h : UG N => ⟪w, σ h (u : H)⟫_ℂ)}
  add_mem' := by
    intro u v hu hv w
    simpa [map_add, inner_add_right] using (hu w).add (hv w)
  zero_mem' := by
    intro w
    simpa using IsPD.const (N := N) 0
  smul_mem' := by
    intro c u hu w
    simpa [map_smul, inner_smul_right] using (IsPD.const c).mul (hu w)

theorem Ugood_eq_top (hrep : IsURepOn (Kset (allPos N)) σ) (hfin : FiniteDimensional ℂ S)
    (hst : IsKStableOn (allPos N) σ S) : Ugood σ S = ⊤ := by
  haveI := hfin
  by_contra hne
  obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  let φC : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap φ
  apply hφ0
  ext u
  let g : UG N → ℂ := fun x => φC (orb hst u x)
  have hg : Continuous g := φC.continuous.comp (orb_cont hrep hst u)
  have hA : ∀ f ∈ algA N, ∫ x, f x * g x ∂(muU N) = 0 := by
    intro f hf
    have hmem : T hst f u ∈ Ugood σ S := fun w => isPositiveDefinite_matrix_coefficient_of_mem_algA hrep hst hf u w
    have h0 : φ (T hst f u) = 0 := LinearMap.mem_ker.mp (hle hmem)
    have hint : Integrable (fun x => f x • orb hst u x) (muU N) :=
      integrable_cont (f.continuous.smul (orb_cont hrep hst u))
    have hc := φC.integral_comp_comm hint
    rw [← h0]
    refine Eq.trans ?_ hc
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [g, φC, map_smul, smul_eq_mul]
  have hall : ∀ F : C(UG N, ℂ), ∫ x, F x * g x ∂(muU N) = 0 := by
    intro F
    have hM0 : 0 ≤ ∫ x, ‖g x‖ ∂(muU N) := integral_nonneg fun x => norm_nonneg _
    have hbound : ∀ ε > 0, ‖∫ x, F x * g x ∂(muU N)‖ ≤ ε * ∫ x, ‖g x‖ ∂(muU N) := by
      intro ε hε
      obtain ⟨f, hf, hfF⟩ := algA_dense N F hε
      have hsplit : ∫ x, F x * g x ∂(muU N) = ∫ x, (F - f) x * g x ∂(muU N) := by
        have h1 : ∫ x, (F - f) x * g x ∂(muU N) =
            ∫ x, F x * g x ∂(muU N) - ∫ x, f x * g x ∂(muU N) := by
          have hi1 : Integrable (fun x => F x * g x) (muU N) := integrable_cont (F.continuous.mul hg)
          have hi2 : Integrable (fun x => f x * g x) (muU N) := integrable_cont (f.continuous.mul hg)
          rw [← integral_sub hi1 hi2]
          congr 1
          funext x
          simp [sub_mul]
        rw [h1, hA f hf, sub_zero]
      rw [hsplit]
      calc ‖∫ x, (F - f) x * g x ∂(muU N)‖ ≤ ∫ x, ‖(F - f) x * g x‖ ∂(muU N) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ε * ‖g x‖ ∂(muU N) := by
          refine integral_mono (integrable_cont (((F - f).continuous.mul hg).norm))
            (integrable_cont (continuous_const.mul hg.norm)) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ((ContinuousMap.norm_coe_le_norm (F - f) x).trans hfF.le)
            (norm_nonneg _)
        _ = ε * ∫ x, ‖g x‖ ∂(muU N) := integral_const_mul _ _
    by_contra hne0
    have hpos : 0 < ‖∫ x, F x * g x ∂(muU N)‖ := norm_pos_iff.mpr hne0
    set I := ‖∫ x, F x * g x ∂(muU N)‖
    set M := ∫ x, ‖g x‖ ∂(muU N)
    have h3 := hbound (I / (M + 1)) (div_pos hpos (by linarith))
    have hlt : I / (M + 1) * M < I := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hF := hall ⟨fun x => star (g x), continuous_star.comp hg⟩
  have hcn : Continuous fun x => Complex.normSq (g x) := Complex.continuous_normSq.comp hg
  have hF' : ∫ x, Complex.normSq (g x) ∂(muU N) = 0 := by
    have h4 : ∫ x, ((Complex.normSq (g x) : ℝ) : ℂ) ∂(muU N) = 0 := by
      rw [← hF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Complex.normSq_eq_conj_mul_self
    rw [integral_complex_ofReal] at h4
    exact_mod_cast h4
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (g x))
    (integrable_cont hcn)).mp hF'
  have heq : (fun x => Complex.normSq (g x)) = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq (muU N) hcn continuous_const).mp hae
  have h1 : Complex.normSq (g 1) = 0 := congrFun heq 1
  rw [Complex.normSq_eq_zero] at h1
  have horb : orb hst u 1 = u := by
    apply Subtype.ext
    simp [orb, hrep.1.1]
  simp only [g, horb] at h1
  simpa [φC] using h1

end

theorem polyCoef : PI.PolyCoef := by
  intro N H _ _ σ S hrep hfin hst v hv w
  have hgood : (⟨v, hv⟩ : S) ∈ Ugood σ S := by
    rw [Ugood_eq_top hrep hfin hst]
    trivial
  obtain ⟨k, P, hP⟩ := hgood w
  refine ⟨k, P, fun g hg => ?_⟩
  exact hP ⟨g, (mem_Kset_iff g).mp hg⟩

end PI.UnitaryGroupMassFormula.PolyCoef
