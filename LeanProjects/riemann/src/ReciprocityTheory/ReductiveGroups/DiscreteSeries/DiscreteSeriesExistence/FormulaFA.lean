import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

section General

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ffa_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  have heq : f =ᶠ[nhdsWithin g₀ (UJset ε)] F := by
    filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg₀U)] with g hg
    exact hfF g hg.2 hg.1
  exact hFc.continuousWithinAt.congr_of_eventuallyEq heq (hfF g₀ hg₀U hg₀)

end Smooth

theorem ffa_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ∃ k' : S7.KG ε, S7.toMK k' = k := by
  obtain ⟨hu, hc⟩ := hk
  have hs : star k * k = 1 := by
    first
    | exact unitary.star_mul_self_of_mem hu
    | exact Unitary.star_mul_self_of_mem hu
    | exact (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hu' : kᴴ * k = 1 := by simpa [Matrix.star_eq_conjTranspose] using hs
  have hUJ : k ∈ UJset ε := by
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu', Matrix.one_mul]
  have hJ : (Jm ε).det ≠ 0 := by
    rw [Jm, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    split_ifs <;> norm_num
  have hdet : IsUnit k.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det (show kᴴ * Jm ε * k = Jm ε from hUJ)
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hJ h.symm
  obtain ⟨y, hy⟩ : ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = k :=
    ⟨⟨Matrix.nonsingInvUnit k hdet, hUJ⟩, rfl⟩
  refine ⟨⟨y, ?_⟩, ?_⟩
  · first
    | exact (show S7.toM y ∈ Kset ε from by rw [show S7.toM y = k from hy]; exact ⟨hu, hc⟩)
    | exact (show Formalism.MainNotions.S.umat y ∈ Kset ε from by rw [hy]; exact ⟨hu, hc⟩)
    | (unfold S7.KG; exact ⟨hu, hc⟩)
  · first
    | exact hy
    | (unfold S7.toMK; exact hy)
    | simpa [S7.toMK, S7.toM] using hy

theorem ffa_UJ_lift {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have hg' : inUJ ε g := hg
  have hJ : (Jm ε).det ≠ 0 := by
    rw [Jm, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    split_ifs <;> norm_num
  have hdet : IsUnit g.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det hg'
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hJ h.symm
  first
  | exact ⟨⟨Matrix.nonsingInvUnit g hdet, hg'⟩, rfl⟩
  | exact ⟨⟨((Matrix.isUnit_iff_isUnit_det g).2 hdet).unit, hg'⟩, rfl⟩

theorem ffa_toMK_mem (k : S7.KG ε) : S7.toMK k ∈ UJset ε := by
  unfold S7.toMK
  exact k.1.2

theorem ffa_cont_toMK : Continuous fun k : S7.KG ε => S7.toMK k := by
  first
  | fun_prop
  | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  | (unfold S7.toMK S7.toM; fun_prop)
  | (unfold S7.toMK; exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))

private theorem isURepOn_rreg' : IsURepOn (UJset ε) (rreg ε) := by
  first
  | exact rreg_isURepOn ε
  | exact rreg_isURepOn
  | exact isURepOn_rreg ε
  | exact isURepOn_rreg
  | exact rreg_isURep ε
  | exact rreg_urep ε
  | exact rreg_rep ε
  | exact rregRep ε

theorem ffa_rreg_mul (k₁ k₂ : S7.KG ε) (x : L2 ε) :
    rreg ε (S7.toMK (k₁ * k₂)) x = rreg ε (S7.toMK k₁) (rreg ε (S7.toMK k₂) x) := by
  have h := (isURepOn_rreg' (ε := ε)).1.2 _ (ffa_toMK_mem k₁) _ (ffa_toMK_mem k₂)
  rw [show S7.toMK (k₁ * k₂) = S7.toMK k₁ * S7.toMK k₂ from rfl, h]
  rfl

theorem ffa_rreg_inv (k : S7.KG ε) (x : L2 ε) : rreg ε (S7.toMK k) (rreg ε (S7.toMK k⁻¹) x) = x := by
  rw [← ffa_rreg_mul, mul_inv_cancel, show S7.toMK (1 : S7.KG ε) = 1 from rfl,
    (isURepOn_rreg' (ε := ε)).1.1]
  rfl

theorem ffa_rreg_inner (k : S7.KG ε) (x y : L2 ε) :
    inner ℂ (rreg ε (S7.toMK k) x) (rreg ε (S7.toMK k) y) = inner ℂ x y := by
  let L : L2 ε →ₗᵢ[ℂ] L2 ε :=
    { toLinearMap := (rreg ε (S7.toMK k)).toLinearMap
      norm_map' := fun v => (isURepOn_rreg' (ε := ε)).2.1 _ (ffa_toMK_mem k) v }
  exact L.inner_map_map x y

theorem ffa_rreg_adj (k : S7.KG ε) (x y : L2 ε) :
    inner ℂ (rreg ε (S7.toMK k) x) y = inner ℂ x (rreg ε (S7.toMK k⁻¹) y) := by
  calc inner ℂ (rreg ε (S7.toMK k) x) y
      = inner ℂ (rreg ε (S7.toMK k) x) (rreg ε (S7.toMK k) (rreg ε (S7.toMK k⁻¹) y)) := by
        rw [ffa_rreg_inv]
    _ = inner ℂ x (rreg ε (S7.toMK k⁻¹) y) := ffa_rreg_inner k x _

theorem ffa_cont_rreg (x : L2 ε) : Continuous fun k : S7.KG ε => rreg ε (S7.toMK k) x := by
  exact ((isURepOn_rreg' (ε := ε)).2.2 x).comp_continuous ffa_cont_toMK ffa_toMK_mem

theorem ffa_intK {E : Type*} [NormedAddCommGroup E] {f : S7.KG ε → E} (hf : Continuous f) :
    Integrable f (dk ε) := by
  exact hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport f) (Set.subset_univ _))

theorem ffa_inner_int (c : S7.KG ε → ℂ) (hc : Continuous c) (x z : L2 ε) :
    inner ℂ z (∫ k, c k • rreg ε (S7.toMK k) x ∂(dk ε)) =
      ∫ k, c k * inner ℂ z (rreg ε (S7.toMK k) x) ∂(dk ε) := by
  have hi : Integrable (fun k => c k • rreg ε (S7.toMK k) x) (dk ε) :=
    ffa_intK (hc.smul (ffa_cont_rreg x))
  rw [← integral_inner hi z]
  simp only [inner_smul_right]

theorem ffa_eval {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : ContinuousOn F (UJset ε)) {x : L2 ε}
    (hx : (x : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun y => F (Formalism.MainNotions.S.umat y))
    (c : S7.KG ε → ℂ) (hc : Continuous c) (h0 : ∫ k, c k • rreg ε (S7.toMK k) x ∂(dk ε) = 0) :
    ∫ k, c k * F (S7.toMK k) ∂(dk ε) = 0 := by
  classical
  have hmem : ∀ (g : Formalism.REAL.UJ ε) (k : S7.KG ε), Formalism.MainNotions.S.umat g * S7.toMK k ∈ UJset ε :=
    fun g k => (g * (@id (Formalism.REAL.UJ ε) k.1)).2
  have hcu : Continuous fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hjoint : Continuous fun p : Formalism.REAL.UJ ε × S7.KG ε =>
      c p.2 * F (Formalism.MainNotions.S.umat p.1 * S7.toMK p.2) :=
    (hc.comp continuous_snd).mul (hF.comp_continuous
      ((hcu.comp continuous_fst).matrix_mul (ffa_cont_toMK.comp continuous_snd)) fun p => hmem p.1 p.2)
  let Φ : Formalism.REAL.UJ ε → ℂ := fun g => ∫ k, c k * F (Formalism.MainNotions.S.umat g * S7.toMK k) ∂(dk ε)
  have hΦc : Continuous Φ := by
    have h := continuous_parametric_integral_of_continuous (μ := dk ε)
      (f := fun (g : Formalism.REAL.UJ ε) (k : S7.KG ε) => c k * F (Formalism.MainNotions.S.umat g * S7.toMK k))
      hjoint isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hS : ∀ S : Set (Formalism.REAL.UJ ε), IsCompact S → ∫ g in S, Φ g ∂(Formalism.REAL.muG ε) = 0 := by
    intro S hSc
    have hSm : MeasurableSet S := hSc.isClosed.measurableSet
    have hSf : Formalism.REAL.muG ε S ≠ ⊤ := hSc.measure_lt_top.ne
    have h1 : inner ℂ (indicatorConstLp 2 hSm hSf (1 : ℂ) : L2 ε)
        (∫ k, c k • rreg ε (S7.toMK k) x ∂(dk ε)) = 0 := by
      rw [h0, inner_zero_right]
    rw [ffa_inner_int c hc x] at h1
    have h2 : ∀ k : S7.KG ε, inner ℂ (indicatorConstLp 2 hSm hSf (1 : ℂ) : L2 ε) (rreg ε (S7.toMK k) x) =
        ∫ g in S, F (Formalism.MainNotions.S.umat g * S7.toMK k) ∂(Formalism.REAL.muG ε) := by
      intro k
      obtain ⟨y, hy⟩ : ∃ y : Formalism.REAL.UJ ε, S7.toMK k = Formalism.MainNotions.S.umat y := ⟨k.1, rfl⟩
      rw [hy, L2.inner_indicatorConstLp_one]
      refine setIntegral_congr_ae hSm ?_
      have e1 := rreg_umat_ae ε y x
      have e2 := (quasiMeasurePreserving_mul_right (Formalism.REAL.muG ε) y).ae_eq hx
      filter_upwards [e1, e2] with g hg1 hg2 _
      rw [hg1]
      simp only [Function.comp_apply] at hg2
      rw [hg2]
      rfl
    have h1' : ∫ k, c k * ∫ g in S, F (Formalism.MainNotions.S.umat g * S7.toMK k) ∂(Formalism.REAL.muG ε) ∂(dk ε) = 0 := by
      refine (integral_congr_ae (ae_of_all _ fun k => ?_)).trans h1
      show c k * _ = c k * _
      rw [h2 k]
    have hint : Integrable (Function.uncurry fun (g : Formalism.REAL.UJ ε) (k : S7.KG ε) =>
        c k * F (Formalism.MainNotions.S.umat g * S7.toMK k)) (((Formalism.REAL.muG ε).restrict S).prod (dk ε)) := by
      have hc2 : IsCompact (S ×ˢ (Set.univ : Set (S7.KG ε))) := hSc.prod isCompact_univ
      have h3 := hjoint.continuousOn.integrableOn_compact (μ := (Formalism.REAL.muG ε).prod (dk ε)) hc2
      rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h3
      exact h3
    show ∫ g in S, (∫ k, c k * F (Formalism.MainNotions.S.umat g * S7.toMK k) ∂(dk ε)) ∂(Formalism.REAL.muG ε) = 0
    rw [integral_integral_swap hint]
    first
    | (simp_rw [integral_const_mul]; exact h1')
    | (simp_rw [integral_mul_left]; exact h1')
  have hae : Φ =ᵐ[Formalism.REAL.muG ε] 0 := by
    first
    | exact ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero hΦc.locallyIntegrable hS
    | exact ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hΦc.locallyIntegrable hS
  have hzero : Φ = 0 := (hΦc.ae_eq_iff_eq (μ := Formalism.REAL.muG ε) continuous_const).1 hae
  have h1 : Φ 1 = 0 := congrFun hzero 1
  have h2 : ∀ k : S7.KG ε, Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) * S7.toMK k = S7.toMK k := fun k => by
    show (1 : Matrix (Fin n) (Fin n) ℂ) * S7.toMK k = S7.toMK k
    exact Matrix.one_mul _
  simpa only [Φ, h2] using h1

end General

section KMap

variable {Λ : Fin n → ℝ}

theorem ffa_op_mul (T : S7.KType ε Λ) (k₁ k₂ : S7.KG ε) : T.op (k₁ * k₂) = T.op k₁ * T.op k₂ := by
  exact congrArg Subtype.val (map_mul T.τ k₁ k₂)

theorem ffa_op_one (T : S7.KType ε Λ) : T.op 1 = 1 := by
  exact congrArg Subtype.val (map_one T.τ)

theorem ffa_op_inner (T : S7.KType ε Λ) (k : S7.KG ε) (x y : T.V) :
    inner ℂ (T.op k x) (T.op k y) = inner ℂ x y := by
  have h1 : ContinuousLinearMap.adjoint (T.op k) * T.op k = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    first
    | exact unitary.star_mul_self_of_mem (T.τ k).2
    | exact Unitary.star_mul_self_of_mem (T.τ k).2
    | exact (unitary.mem_iff.1 (T.τ k).2).1
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, h1,
    ContinuousLinearMap.one_apply]

theorem ffa_op_inv_apply (T : S7.KType ε Λ) (k : S7.KG ε) (y : T.V) : T.op k (T.op k⁻¹ y) = y := by
  rw [← ContinuousLinearMap.mul_apply, ← ffa_op_mul]
  simp [ffa_op_one]

theorem ffa_op_adj' (T : S7.KType ε Λ) (k : S7.KG ε) (x y : T.V) :
    inner ℂ x (T.op k y) = inner ℂ (T.op k⁻¹ x) y := by
  rw [← ffa_op_inner T k (T.op k⁻¹ x) y, ffa_op_inv_apply]

theorem ffa_cont_coef (T : S7.KType ε Λ) (a v : T.V) :
    Continuous fun k : S7.KG ε => inner ℂ (T.op k a) v := by
  have h1 : Continuous fun k : S7.KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (h1.clm_apply continuous_const).inner continuous_const

def ffaB (T : S7.KType ε Λ) (a : T.V) (x : L2 ε) : T.V →ₗ[ℂ] L2 ε where
  toFun v := ∫ k, inner ℂ (T.op k a) v • rreg ε (S7.toMK k) x ∂(dk ε)
  map_add' v w := by
    simp only [inner_add_right, add_smul]
    exact integral_add (ffa_intK ((ffa_cont_coef T a v).smul (ffa_cont_rreg x)))
      (ffa_intK ((ffa_cont_coef T a w).smul (ffa_cont_rreg x)))
  map_smul' c v := by
    simp only [inner_smul_right, mul_smul, RingHom.id_apply]
    exact integral_smul c _

theorem ffaB_apply (T : S7.KType ε Λ) (a : T.V) (x : L2 ε) (v : T.V) :
    ffaB T a x v = ∫ k, inner ℂ (T.op k a) v • rreg ε (S7.toMK k) x ∂(dk ε) := rfl

theorem ffaB_equiv (T : S7.KType ε Λ) (a : T.V) (x : L2 ε) (k₀ : S7.KG ε) (v : T.V) :
    ffaB T a x (T.op k₀ v) = rreg ε (S7.toMK k₀) (ffaB T a x v) := by
  rw [ffaB_apply, ffaB_apply]
  have h1 : ∀ k : S7.KG ε, inner ℂ (T.op k a) (T.op k₀ v) = inner ℂ (T.op (k₀⁻¹ * k) a) v := fun k => by
    rw [ffa_op_adj', ffa_op_mul, ContinuousLinearMap.mul_apply]
  simp_rw [h1]
  have h2 := integral_mul_left_eq_self (μ := dk ε)
    (fun k => inner ℂ (T.op (k₀⁻¹ * k) a) v • rreg ε (S7.toMK k) x) k₀
  rw [← h2]
  simp only [inv_mul_cancel_left, ffa_rreg_mul]
  have hi : Integrable (fun k => inner ℂ (T.op k a) v • rreg ε (S7.toMK k) x) (dk ε) :=
    ffa_intK ((ffa_cont_coef T a v).smul (ffa_cont_rreg x))
  rw [← (rreg ε (S7.toMK k₀)).integral_comp_comm hi]
  simp only [map_smul]

theorem ffaB_inner (T : S7.KType ε Λ) (a : T.V) (x z : L2 ε) (v : T.V) :
    inner ℂ z (ffaB T a x v) = ∫ k, inner ℂ (T.op k a) v * inner ℂ z (rreg ε (S7.toMK k) x) ∂(dk ε) := by
  rw [ffaB_apply]
  exact ffa_inner_int (fun k => inner ℂ (T.op k a) v) (ffa_cont_coef T a v) x z

theorem ffaB_mem (T : S7.KType ε Λ) (a : T.V) (x : L2 ε) (S : Submodule ℂ (L2 ε))
    [S.HasOrthogonalProjection] (hS : ∀ k : S7.KG ε, rreg ε (S7.toMK k) x ∈ S) (v : T.V) :
    ffaB T a x v ∈ S := by
  rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
  intro z hz
  rw [ffaB_inner]
  have h0 : ∀ k : S7.KG ε, inner ℂ z (rreg ε (S7.toMK k) x) = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hS k) hz
  simp only [h0, mul_zero, integral_zero]

end KMap

section Psi

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem ffa_memLp (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    MemLp (fun y : Formalism.REAL.UJ ε => jfun Ψ u v (Formalism.MainNotions.S.umat y)) 2 (Formalism.REAL.muG ε) := by
  have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  have h := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
  have h2 := ((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h
  refine MemLp.ae_eq (ae_of_all _ fun y => ?_) h2
  simp [jfun]
  try rfl

theorem uniformisationL2_ae_eq_jfun (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    (uniformisationL2 ε Ψ u v : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun y => jfun Ψ u v (Formalism.MainNotions.S.umat y) := by
  unfold uniformisationL2 toL2
  rw [dif_pos (ffa_memLp hP u v)]
  exact (ffa_memLp hP u v).coeFn_toLp

theorem ffa_jfun_cont (hP : IsPsiFor ε lam T Ψ) (u v : T.V) : ContinuousOn (jfun Ψ u v) (UJset ε) := by
  have hΨ : ContinuousOn Ψ (UJset ε) := ffa_continuousOn hP.2.2.1
  unfold jfun
  exact continuousOn_const.inner (hΨ.clm_apply continuousOn_const)

def ffaJ (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε :=
  ⟨⟨uniformisationL2 ε Ψ v₀, datumEmbedding_add hP v₀⟩, datumEmbedding_smul hP v₀⟩

theorem ffaJ_apply (hP : IsPsiFor ε lam T Ψ) (v₀ u : T.V) : ffaJ hP v₀ u = uniformisationL2 ε Ψ v₀ u := rfl

def ffaJinv (hP : IsPsiFor ε lam T Ψ) (x : datumV ε Ψ v₀) : T.V :=
  ((mem_datumV_iff hP v₀ (x : smD ε (rreg ε))).1 x.2).choose

theorem ffaJinv_spec (hP : IsPsiFor ε lam T Ψ) (x : datumV ε Ψ v₀) :
    uniformisationL2 ε Ψ v₀ (ffaJinv hP x) = ((x : smD ε (rreg ε)) : L2 ε) :=
    ((mem_datumV_iff hP v₀ (x : smD ε (rreg ε))).1 x.2).choose_spec.symm

def ffaJinvL (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : datumV ε Ψ v₀ →ₗ[ℂ] T.V where
  toFun := ffaJinv hP
  map_add' x y := uniformisationL2_injective hP hv₀ (by
    rw [datumEmbedding_add hP, ffaJinv_spec, ffaJinv_spec, ffaJinv_spec]; try rfl)
  map_smul' c x := uniformisationL2_injective hP hv₀ (by
    rw [datumEmbedding_smul hP, ffaJinv_spec, ffaJinv_spec]; try rfl)

private theorem inner_uniformisationL2_eq_norm_sq_mul_inner (hP : IsPsiFor ε lam T Ψ) (v' u : T.V) :
    inner ℂ (uniformisationL2 ε Ψ v₀ v') (uniformisationL2 ε Ψ v₀ u) = ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' u := by
  let J : T.V →L[ℂ] L2 ε := LinearMap.toContinuousLinearMap (ffaJ hP v₀)
  have hJ : ∀ v, J v = uniformisationL2 ε Ψ v₀ v := fun v => rfl
  let A : T.V →L[ℂ] T.V := (ContinuousLinearMap.adjoint J).comp J
  have hA : ∀ a b : T.V, inner ℂ a (A b) = inner ℂ (uniformisationL2 ε Ψ v₀ a) (uniformisationL2 ε Ψ v₀ b) := by
    intro a b
    show inner ℂ a ((ContinuousLinearMap.adjoint J) (J b)) = _
    rw [ContinuousLinearMap.adjoint_inner_right, hJ, hJ]
  have hcomm : ∀ k, T.op k * A = A * T.op k := by
    intro k
    refine ContinuousLinearMap.ext fun b => ?_
    refine ext_inner_left ℂ fun a => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ffa_op_adj' T k a (A b), hA, hA,
      ← rightRegular_datumEmbedding hP v₀ a k⁻¹, ← rightRegular_datumEmbedding hP v₀ b k, ffa_rreg_adj, inv_inv]
  obtain ⟨c, hc⟩ := CompactHaarProbability.schur T A hcomm
  have hform : ∀ a b : T.V, inner ℂ (uniformisationL2 ε Ψ v₀ a) (uniformisationL2 ε Ψ v₀ b) = c * inner ℂ a b := by
    intro a b
    rw [← hA, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
  have hc' : c = ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) := by
    have h1 := hform T.w T.w
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, T.w_norm] at h1
    first
    | (push_cast at h1 ⊢; linear_combination -h1)
    | (simp only [one_pow, mul_one, map_one] at h1; push_cast; exact h1.symm.trans (by push_cast; ring))
    | (simp at h1 ⊢; linear_combination -h1)
  rw [hform, hc']

theorem ffa_kmap_zero (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (B : T.V →ₗ[ℂ] L2 ε) (hB : ∀ (k : S7.KG ε) (v : T.V), B (T.op k v) = rreg ε (S7.toMK k) (B v))
    (hrange : ∀ v, B v ∈ Hlam ε Ψ v₀)
    (horth : ∀ v v' : T.V, inner ℂ (B v') (uniformisationL2 ε Ψ v₀ v) = 0) : B = 0 := by
  classical
  let J : T.V →L[ℂ] L2 ε := LinearMap.toContinuousLinearMap (ffaJ hP v₀)
  let Jd : L2 ε →L[ℂ] T.V := ContinuousLinearMap.adjoint J
  have hJd : ∀ (y : L2 ε) (v : T.V), inner ℂ v (Jd y) = inner ℂ (uniformisationL2 ε Ψ v₀ v) y := by
    intro y v
    rw [ContinuousLinearMap.adjoint_inner_right]
    rfl
  have hJdk : ∀ (k : S7.KG ε) (y : L2 ε), Jd (rreg ε (S7.toMK k) y) = T.op k (Jd y) := by
    intro k y
    refine ext_inner_left ℂ fun v => ?_
    rw [hJd, ffa_op_adj' T k v (Jd y), hJd, ← rightRegular_datumEmbedding hP v₀ v k⁻¹, ffa_rreg_adj, inv_inv]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hJdJ : ∀ v, Jd (uniformisationL2 ε Ψ v₀ v) = c • v := by
    intro v
    refine ext_inner_left ℂ fun u => ?_
    rw [hJd, inner_uniformisationL2_eq_norm_sq_mul_inner hP u v, inner_smul_right, hc]
  have hw0 : T.w ≠ 0 := by
    intro h
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hc0 : c ≠ 0 := by
    have hj : uniformisationL2 ε Ψ v₀ T.w ≠ 0 := by
      intro h
      apply hw0
      apply uniformisationL2_injective hP hv₀
      rw [h]
      exact (map_zero (ffaJ hP v₀)).symm
    rw [hc]
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 hj))
  let φ : Hlam ε Ψ v₀ →ₗ[ℂ] Hlam ε Ψ v₀ :=
    LinearMap.id + (B.codRestrict (Hlam ε Ψ v₀) hrange).comp
      ((Jd : L2 ε →ₗ[ℂ] T.V).comp (Hlam ε Ψ v₀).subtype)
  have hφ : ∀ x : Hlam ε Ψ v₀, ((φ x : Hlam ε Ψ v₀) : L2 ε) = (x : L2 ε) + B (Jd (x : L2 ε)) := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (x : L2 ε) + B (Jd (x : L2 ε)) = 0 := by
      rw [← hφ, hx]
      rfl
    have hxe : (x : L2 ε) = -B (Jd (x : L2 ε)) := eq_neg_of_add_eq_zero_left hx'
    have hJx : Jd (x : L2 ε) = 0 := by
      refine ext_inner_left ℂ fun v => ?_
      rw [hJd, inner_zero_right, hxe, inner_neg_right, ← inner_conj_symm, horth, map_zero, neg_zero]
    apply Subtype.ext
    rw [hJx, map_zero, add_zero] at hx'
    exact hx'
  have hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, φ (sigLam ε Ψ v₀ g x) = sigLam ε Ψ v₀ g (φ x) := by
    intro g hg x
    have h1 := subtype_sigLam hgap hP hv₀ g hg x
    have h2 := subtype_sigLam hgap hP hv₀ g hg (φ x)
    obtain ⟨k, hk⟩ : ∃ k : S7.KG ε, S7.toMK k = g := by
      first
      | exact ffa_Kset hg
      | exact ffa_Kset (by rw [← mir_Kset_eq]; exact hg)
      | exact ffa_Kset (by simpa [Kset, Formalism.REAL.Kset] using hg)
    apply Subtype.ext
    simp only [Submodule.coe_subtype] at h1 h2
    rw [h2, hφ, hφ, h1, ← hk, hJdk, hB, map_add]
  have hK := sigLam_lowK hgap hP hv₀
  have hmap : Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ v₀) (Formalism.QuantumDeterminants.lowK ε lam) ((lowKSubLam ε Ψ v₀).map φ) :=
    (isKTypeOf_map_iff φ hinj hint _ _).1 hK.1
  have heq := hK.2 _ hmap
  have hlow : ∀ y : Hlam ε Ψ v₀, y ∈ lowKSubLam ε Ψ v₀ →
      (y : L2 ε) ∈ Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) := by
    intro y hy
    have hy' : (Hlam ε Ψ v₀).subtype y ∈ (datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype := hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : (z : L2 ε) ∈ Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) := hz
    have hzy' : (z : L2 ε) = (y : L2 ε) := hzy
    rw [← hzy']
    exact hz'
  have hJlow : ∀ v, (⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ v₀) ∈ lowKSubLam ε Ψ v₀ := by
    intro v
    show (Hlam ε Ψ v₀).subtype ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩ ∈
      (datumV ε Ψ v₀).map (smD ε (rreg ε)).subtype
    exact ⟨⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩, Submodule.subset_span ⟨v, rfl⟩, rfl⟩
  have hspan : ∀ v, Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) ≤ LinearMap.ker ((innerSL ℂ (B v) : L2 ε →L[ℂ] ℂ) : L2 ε →ₗ[ℂ] ℂ) := by
    intro v
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    first
    | exact horth u v
    | exact LinearMap.mem_ker.2 (by simpa using horth u v)
  refine LinearMap.ext fun v => ?_
  have hmem : φ ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩ ∈ lowKSubLam ε Ψ v₀ := by
    rw [← heq]
    exact Submodule.mem_map_of_mem (hJlow v)
  have h1 := hlow _ hmem
  have h2 := hlow _ (hJlow v)
  rw [hφ] at h1
  have h3 : c • B v ∈ Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) := by
    have h4 := Submodule.sub_mem _ h1 h2
    have h5 : uniformisationL2 ε Ψ v₀ v + B (Jd (uniformisationL2 ε Ψ v₀ v)) - uniformisationL2 ε Ψ v₀ v = c • B v := by
      rw [hJdJ, map_smul, add_sub_cancel_left]
    rw [← h5]
    exact h4
  have h6 : inner ℂ (B v) (c • B v) = 0 := by
    first
    | exact hspan v h3
    | simpa using LinearMap.mem_ker.1 (hspan v h3)
  rw [inner_smul_right] at h6
  have h7 : inner ℂ (B v) (B v) = 0 := (mul_eq_zero.1 h6).resolve_left hc0
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 h7

theorem ffa_form (hP : IsPsiFor ε lam T Ψ) (v' u : T.V) :
    inner ℂ (uniformisationL2 ε Ψ v₀ v') (uniformisationL2 ε Ψ v₀ u) = ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' u := by
  exact inner_uniformisationL2_eq_norm_sq_mul_inner hP v' u

end Psi

end ReciprocityTheory.ChartRestriction.DS
