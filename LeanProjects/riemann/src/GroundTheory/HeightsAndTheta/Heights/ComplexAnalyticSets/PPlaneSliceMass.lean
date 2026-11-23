import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaneSliceMass
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFubiniStudyChartDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

abbrev affChartIdeal (e : ℕ) : Ideal (MvPolynomial (Fin (e + 1)) ℂ) := Ideal.span {X 0 - 1}

def tailProj (e : ℕ) : Matrix (Fin e) (Fin (e + 1)) ℂ := fun i j => if j = i.succ then 1 else 0

theorem tailProj_mulVec (e : ℕ) (x : Fin (e + 1) → ℂ) : tailProj e *ᵥ x = Fin.tail x := by
  ext i
  simp [tailProj, Matrix.mulVec, dotProduct, Fin.tail]

theorem linPoly_tailProj (e : ℕ) (i : Fin e) : linPoly (tailProj e) i = X i.succ := by
  simp [linPoly, tailProj]

def affChartEquiv (e : ℕ) : MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e ≃+* MvPolynomial (Fin e) ℂ :=
  (Ideal.quotientEquiv _ _ (finSuccEquiv ℂ e).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      simp [finSuccEquiv_X_zero])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (1 : MvPolynomial (Fin e) ℂ)).toRingEquiv

theorem affChartEquiv_projHom (e : ℕ) (a : MvPolynomial (Fin e) ℂ) :
    affChartEquiv e (projHom (affChartIdeal e) (tailProj e) a) = a := by
  have h : (affChartEquiv e : _ →+* MvPolynomial (Fin e) ℂ).comp
      (projHom (affChartIdeal e) (tailProj e)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : (finSuccEquiv ℂ e) (C c) = algebraMap ℂ _ c := (finSuccEquiv ℂ e).commutes c
      simp [affChartEquiv, projHom, pullback, Polynomial.quotientSpanXSubCAlgEquiv_mk, hc,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro i
      simp [affChartEquiv, projHom, pullback, linPoly_tailProj,
        Polynomial.quotientSpanXSubCAlgEquiv_mk, finSuccEquiv_X_succ]
  exact RingHom.congr_fun h a

theorem isFiniteProjection_tailProj (e : ℕ) : IsFiniteProjection (affChartIdeal e) (tailProj e) := by
  refine ⟨fun a b h => ?_, RingHom.Finite.of_surjective _ fun z => ⟨affChartEquiv e z, ?_⟩⟩
  · have := congrArg (affChartEquiv e) h
    rwa [affChartEquiv_projHom, affChartEquiv_projHom] at this
  · exact (affChartEquiv e).injective (affChartEquiv_projHom e _)

theorem affChartIdeal_isPrime (e : ℕ) : (affChartIdeal e).IsPrime := by
  have : IsDomain (MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e) := (affChartEquiv e).toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

theorem affChartIdeal_dim (e : ℕ) :
    ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e) = (e : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (affChartEquiv e), MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simp

theorem mem_zeroSet_affChartIdeal {e : ℕ} (x : Fin (e + 1) → ℂ) : x ∈ zeroSet (affChartIdeal e) ↔ x 0 = 1 := by
  constructor
  · intro h
    have := h _ (Ideal.subset_span rfl)
    simpa [sub_eq_zero] using this
  · intro h q hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    simp [h]

theorem fibre_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    fibre (affChartIdeal e) (tailProj e) y = {(Fin.cons 1 y : Fin (e + 1) → ℂ)} := by
  ext x
  simp only [fibre, Set.mem_ofPred_eq, mem_zeroSet_affChartIdeal, Set.mem_singleton_iff]
  rw [tailProj_mulVec]
  constructor
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail x, h0, ht]
  · rintro rfl
    simp

theorem differentiable_consOne (e : ℕ) :
    Differentiable ℂ (fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ)) := by
  intro y
  rw [differentiableAt_pi]
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simpa using differentiableAt_apply (𝕜 := ℂ) i y

theorem isSheetAt_consOne {e : ℕ} (y : Fin e → ℂ) :
    IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ) := by
  refine ⟨Set.univ, isOpen_univ, trivial, (differentiable_consOne e).differentiableOn, ?_,
    fun y' _ => ⟨?_, ?_⟩, Set.univ, univ_mem, fun x' hx' _ => ?_⟩
  · rw [tailProj_mulVec, Fin.tail_cons]
  · rw [tailProj_mulVec, Fin.tail_cons]
  · rw [mem_zeroSet_affChartIdeal]
    rfl
  · rw [tailProj_mulVec]
    conv_lhs => rw [← Fin.cons_self_tail x']
    rw [(mem_zeroSet_affChartIdeal x').1 hx'.1]

theorem affChart_sheet_eventuallyEq {e : ℕ} {y : Fin e → ℂ} {s : (Fin e → ℂ) → Fin (e + 1) → ℂ}
    (h : IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) s) :
    s =ᶠ[𝓝 y] fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ) := by
  obtain ⟨U, hU, hyU, -, -, hsec, -⟩ := h
  rw [tailProj_mulVec, Fin.tail_cons] at hyU
  filter_upwards [hU.mem_nhds hyU] with y' hy'
  obtain ⟨h1, h2⟩ := hsec y' hy'
  rw [tailProj_mulVec] at h1
  rw [mem_zeroSet_affChartIdeal] at h2
  rw [← Fin.cons_self_tail (s y'), h2, h1]

theorem sheetSum_affChartIdeal {e : ℕ} (F : (Fin (e + 1) → ℂ) → ((Fin e → ℂ) → Fin (e + 1) → ℂ) → ℝ)
    (y : Fin e → ℂ) (hF : ∀ s, s =ᶠ[𝓝 y] (fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ)) →
      F (Fin.cons 1 y) s = F (Fin.cons 1 y) fun y' => Fin.cons 1 y') :
    sheetSum (affChartIdeal e) (tailProj e) F y = F (Fin.cons 1 y) fun y' => Fin.cons 1 y' := by
  unfold sheetSum
  rw [fibre_affChartIdeal, finsum_mem_singleton]
  have hex : ∃ s, IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) s := ⟨_, isSheetAt_consOne y⟩
  rw [dif_pos hex]
  exact hF _ (affChart_sheet_eventuallyEq hex.choose_spec)

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

theorem dualNorm_std {n : ℕ} (x : Fin n → ℂ) : (HermNorm.std n).dualNorm x = √(∑ i, ‖x i‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

theorem log_dualNorm_consOne {e : ℕ} (y : Fin e → ℂ) :
    Real.log ((HermNorm.std (e + 1)).dualNorm (Fin.cons 1 y)) =
      (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2) := by
  rw [dualNorm_std, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, norm_one, one_pow]
  rw [Real.log_sqrt (by positivity)]
  ring

def fsChartDens (e : ℕ) (y : Fin e → ℂ) : ℝ :=
  (e.factorial : ℝ) / (Real.pi ^ e * (1 + ∑ i, ‖y i‖ ^ 2) ^ (e + 1))

theorem fsChartDens_nonneg {e : ℕ} (y : Fin e → ℂ) : 0 ≤ fsChartDens e y := by
  unfold fsChartDens
  have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
  have := Real.pi_pos
  positivity

theorem maDens_consOne {e : ℕ} (y : Fin e → ℂ) (s : (Fin e → ℂ) → Fin (e + 1) → ℂ)
    (hs : s =ᶠ[𝓝 y] fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ)) :
    ReciprocityTheory.AnForm.maDens
        (fun k => (fun (_ : Fin e) x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) k ∘ s) y =
      fsChartDens e y := by
  rw [maDens_congr (G := fun _ y' => (1 / 2) * Real.log (1 + ∑ i, ‖y' i‖ ^ 2)) fun k => ?_]
  · exact (FourB.FubiniStudyChartDensity.proof e y y).2
  · filter_upwards [hs] with y' hy'
    simp only [Function.comp_apply, hy', log_dualNorm_consOne]

theorem chartDens_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    chartDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) y = fsChartDens e y := by
  unfold chartDens
  rw [sheetSum_affChartIdeal _ y fun s hs => by rw [maDens_consOne y s hs,
    maDens_consOne y _ (EventuallyEq.refl _ _)]]
  rw [one_mul, maDens_consOne y _ (EventuallyEq.refl _ _)]

theorem chartAbsDens_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    chartAbsDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) y = fsChartDens e y := by
  unfold chartAbsDens
  rw [sheetSum_affChartIdeal _ y fun s hs => by rw [maDens_consOne y s hs,
    maDens_consOne y _ (EventuallyEq.refl _ _)]]
  rw [one_mul, maDens_consOne y _ (EventuallyEq.refl _ _), abs_of_nonneg (fsChartDens_nonneg y)]

theorem integral_fsChartDens (e : ℕ) : ∫ y, fsChartDens e y = 1 := by
  have h : fsChartDens e = fun y => ((e.factorial : ℝ) / Real.pi ^ e) *
      ((1 + ∑ i, ‖y i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [fsChartDens, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [h, integral_const_mul, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integral_fsDens]
  have : (e.factorial : ℝ) ≠ 0 := by positivity
  have : Real.pi ^ e ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp

theorem integrable_fsChartDens (e : ℕ) : Integrable (fsChartDens e) :=
  Integrable.of_integral_ne_zero (by rw [integral_fsChartDens]; exact one_ne_zero)

theorem smoothNear_log_dualNorm (e : ℕ) :
    SmoothNear (zeroSet (affChartIdeal e)) fun x => Real.log ((HermNorm.std (e + 1)).dualNorm x) := by
  refine ⟨{x | x 0 ≠ 0}, isOpen_ne_fun (continuous_apply 0) continuous_const, fun x hx => ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, (mem_zeroSet_affChartIdeal x).1 hx]
    exact one_ne_zero
  · intro x hx
    have h0 : 0 < ‖x 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have hpos : 0 < euclPot x :=
      lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ 0))
    have hf : (fun x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) =
        fun x => Real.log (√(euclPot x)) := funext fun x => by rw [dualNorm_std]; rfl
    rw [hf]
    refine ContDiffAt.contDiffWithinAt ?_
    exact (Real.contDiffAt_log.2 (Real.sqrt_pos.2 hpos).ne').comp x
      ((Real.contDiffAt_sqrt hpos.ne').comp x (contDiff_euclPot _).contDiffAt)

theorem PlaneSliceMass.proof (h₁ : IntegralIndep.Statement) : PlaneSliceMass.Statement := by
  intro e
  have hex : ∃ A : Matrix (Fin e) (Fin (e + 1)) ℂ, IsFiniteProjection (affChartIdeal e) A :=
    ⟨_, isFiniteProjection_tailProj e⟩
  show varInt (affChartIdeal e) e _ _ = 1
  unfold varInt
  rw [dif_pos hex]
  have habs : Integrable (chartAbsDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) := by
    rw [funext chartAbsDens_affChartIdeal]
    exact integrable_fsChartDens e
  obtain ⟨-, heq⟩ := h₁ (e + 1) e _ (tailProj e) hex.choose _ _ (affChartIdeal_isPrime e)
    (affChartIdeal_dim e) (isFiniteProjection_tailProj e) hex.choose_spec measurable_const
    (fun _ => smoothNear_log_dualNorm e) habs
  rw [← heq, chartInt, funext chartDens_affChartIdeal, integral_fsChartDens]

end

end GroundTheory.Heights₂.Heights
