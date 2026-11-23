import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapRDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MovedPointDeterminant
open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Global
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem cv_mod (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w => by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, hm]

private theorem cv_sum (x : Cinf E) : ∑ τ : E →+* ℂ, coord τ x = ∑ w : InfinitePlace E, (x w + starRingEnd ℂ (x w)) := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun τ : E →+* ℂ => InfinitePlace.mk τ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w) (InfinitePlace.isReal_iff.2 h)
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · right
        rw [h]
        exact (ComplexEmbedding.involutive_conjugate E τ).symm
    · rintro (rfl | rfl) <;> simp
  rw [hf, Finset.sum_pair hne.symm]
  unfold coord
  simp [hne.symm]

private theorem cv_det {m : ℝ → Matrix (Fin a) (Fin a) ℂ} {Y : Matrix (Fin a) (Fin a) ℂ} (h0 : m 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun s => m s i j) (Y i j) 0) : HasDerivAt (fun s => (m s).det) (∑ i, Y i i) 0 :=
  _root_.UpperTheory.Reformulated.B.MovedPointDeterminant.cv_det h0 hd

end

theorem UpperTheory.one_parameter_subgroup_norm_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r : ℕ) (X : Lie E r), ∑ τ : E →+* ℂ, ∑ i, coord τ (X i i) = 0 →
          ∃ c : ℝ → GL (Fin r) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous (fun s => infGL E r (c s)) ∧
            HasDerivAt (fun s => toL (c s).val) X 0 ∧ ∀ s, infGL E r (c s) ∈ normOneGL E r := by
  intro E _ _ _ r X hX
  classical
  obtain ⟨c, h0, hadd, hc, hd, -⟩ := UpperTheory.V.Lit.Bor.oneParam E r X
  refine ⟨c, h0, hadd, hc, hd, fun s => ?_⟩
  have hD : ∀ w : InfinitePlace E, HasDerivAt (fun s => (c s).val.det w) (∑ i, X i i w) 0 := fun w => by
    have h1 := cv_det (m := fun s => (c s).val.map fun x => x w) (Y := fun i j => X i j w)
      (by rw [h0]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h])
      fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hd i) j) w
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    exact RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (c s).val
  let Q : ℝ → ℂ := fun s => ∏ w : InfinitePlace E, ((c s).val.det w * starRingEnd ℂ ((c s).val.det w))
  have hQ0 : Q 0 = 1 := by simp [Q, h0]
  have hQm : ∀ s t, Q (s + t) = Q s * Q t := fun s t => by
    simp only [Q, hadd, Units.val_mul, Matrix.det_mul, Pi.mul_apply, map_mul, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => by ring
  have hQd : HasDerivAt Q 0 0 := by
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ) fun (w : InfinitePlace E) _ => (hD w).fun_mul (hD w).star
    refine h.congr_deriv (Eq.symm ?_)
    rw [Finset.sum_comm] at hX
    simp only [cv_sum] at hX
    rw [Finset.sum_comm] at hX
    refine hX.symm.trans ?_
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [h0, Finset.sum_add_distrib]
  have hall : ∀ t, HasDerivAt Q 0 t := fun t => by
    have h1 : HasDerivAt (fun u => Q (u - t)) 0 t := by
      have := HasDerivAt.scomp t (g₁ := Q) (h := fun u => u - t) (by simpa using hQd) ((hasDerivAt_id t).sub_const t)
      simpa [Function.comp_def] using this
    have h2 := h1.const_mul (Q t)
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    change Q u = Q t * Q (u - t)
    rw [← hQm, add_sub_cancel]
  have hQ : Q s = 1 := (is_const_of_deriv_eq_zero (fun t => (hall t).differentiableAt) (fun t => (hall t).deriv) s 0).trans hQ0
  refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
  refine (cv_mod (c s)).trans ?_
  simp only [Q, Complex.mul_conj'] at hQ
  exact_mod_cast hQ
