import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSheetNoRatNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace ChartSheetNoRatNull

variable {n d : ℕ}

theorem differentiable_eval (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun z : Fin n → ℂ => eval z P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_poly_of_not_mem {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hq : q ∉ J) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ x ∈ zeroSet J, eval x q = 0 → eval (A *ᵥ x) c = 0 := by
  classical
  have hv0 : Ideal.Quotient.mk J q ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hq
  have hex : ∃ k, ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧ P.natDegree = k ∧
      P.eval₂ (projHom J A).toRingHom (Ideal.Quotient.mk J q) = 0 := by
    obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J q)
    exact ⟨_, P, hPm, rfl, hP⟩
  obtain ⟨P, hPm, hPk, hP⟩ := Nat.find_spec hex
  have hc0 : P.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨Q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hQm : Q.Monic := Polynomial.monic_X.of_mul_monic_left hPm
    have hdeg : (Polynomial.X * Q).natDegree = Q.natDegree + 1 :=
      Polynomial.natDegree_X_mul hQm.ne_zero
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_eq_zero] at hP
    refine Nat.find_min hex (m := Q.natDegree) (by omega) ⟨Q, hQm, rfl, ?_⟩
    exact hP.resolve_left hv0
  have hQ : Ideal.Quotient.mk J (P.eval₂ (pullback A).toRingHom q) = 0 := by
    rw [Polynomial.hom_eval₂]; exact hP
  have hQJ := Ideal.Quotient.eq_zero_iff_mem.1 hQ
  refine ⟨P.coeff 0, hc0, fun x hx hqx => ?_⟩
  have h1 : eval x (P.eval₂ (pullback A).toRingHom q) = 0 := hx _ hQJ
  rw [Polynomial.hom_eval₂, hqx, Polynomial.eval₂_at_zero] at h1
  have h2 : eval x (pullback A (P.coeff 0)) = 0 := h1
  rwa [ComplexSets.eval_pullback] at h2

theorem volume_image_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A) (hq : q ∉ J) :
    volume ((fun x => A *ᵥ x) '' {x | x ∈ zeroSet J ∧ eval x q = 0}) = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_poly_of_not_mem hJ hA hq
  refine measure_mono_null ?_ (DiscriminantSheetCover.volume_zero_set c hc)
  rintro _ ⟨x, ⟨hx, hqx⟩, rfl⟩
  exact hcz x hx hqx

theorem isOpen_dom {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ} (q : MvPolynomial (Fin n) ℂ)
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U) : IsOpen (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
  hsd.continuousOn.isOpen_inter_preimage hU
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const)

theorem differentiableOn_ratMap_comp {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (hsd : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => RatChart.ratMap p q (s w)) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) := by
  rw [differentiableOn_pi]
  intro r
  have hs' := hsd.mono (Set.inter_subset_left (t := s ⁻¹' {x | eval x q ≠ 0}))
  have hnum : DifferentiableOn ℂ (fun w => eval (s w) (p r)) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
    (differentiable_eval (p r)).comp_differentiableOn hs'
  have hden : DifferentiableOn ℂ (fun w => eval (s w) q) (U ∩ s ⁻¹' {x | eval x q ≠ 0}) :=
    (differentiable_eval q).comp_differentiableOn hs'
  show DifferentiableOn ℂ (fun w => eval (s w) (p r) / eval (s w) q) _
  simp only [div_eq_mul_inv]
  exact hnum.mul (hden.inv fun w hw => hw.2)

theorem exists_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hsd : DifferentiableOn ℂ s U) (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hW₀D : W₀ ⊆ U ∩ s ⁻¹' {x | eval x q ≠ 0})
    (hne : W₀.Nonempty) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => RatChart.ratMap p q (s w)) w).det ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨y, hy⟩ := CriticalFibreInfinite.proof d d W₀ (fun w => RatChart.ratMap p q (s w)) hW₀ hne
    ((differentiableOn_ratMap_comp p q hsd).mono hW₀D)
    (fun t ht hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall t ht))
  refine hy (Set.Finite.of_finite_image (f := s) ((hfin y).subset ?_) ?_)
  · rintro _ ⟨t, ⟨htW, hty⟩, rfl⟩
    exact ⟨(hsec t (hW₀D htW).1).2, (hW₀D htW).2, hty⟩
  · intro a ha b hb hab
    rw [← (hsec a (hW₀D ha.1).1).1, ← (hsec b (hW₀D hb.1).1).1]
    exact congrArg _ hab

theorem exists_ratSheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (hqx : eval x q ≠ 0)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => RatChart.ratMap p q (s w)) (A *ᵥ x)).det ≠ 0) :
    ∃ s', RatChart.IsRatSheetAt J p q x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set D := U ∩ s ⁻¹' {x | eval x q ≠ 0} with hDdef
  have hD : IsOpen D := isOpen_dom q hU hsd
  have hyD : A *ᵥ x ∈ D := ⟨hyU, by simp only [Set.mem_preimage, hsx]; exact hqx⟩
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => RatChart.ratMap p q (s w) with hFdef
  have hFd : DifferentiableOn ℂ F D := differentiableOn_ratMap_comp p q hsd
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hD hFd
  set G : Set (Fin d → ℂ) := D ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (SheetOnlyNull.analyticOnNhd_det_jacC hD hFd).continuousOn
    |>.isOpen_inter_preimage hD isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyD, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = RatChart.ratMap p q x := by simp only [hFdef, hsx]
  have hsym : φ.symm (RatChart.ratMap p q x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyD, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx],
    fun z hz => ⟨(hsec _ hz.2.1.1).2, hz.2.1.2, ?_⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ D), inter_mem hV
      (((φ.open_source.inter hD).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyD⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''D⟩ - -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''D.1
    have hR : RatChart.ratMap p q x'' = φ (A *ᵥ x'') := by
      rw [hφ]
      show RatChart.ratMap p q x'' = RatChart.ratMap p q (s (A *ᵥ x''))
      exact congrArg _ hx''
    rw [Function.comp_apply, hR, φ.left_inv hx''src]
    exact hx''

end ChartSheetNoRatNull

open ChartSheetNoRatNull in

theorem ChartSheetNoRatNull.proof : ChartSheetNoRatNull.Statement := by
  intro n d J A p q hJ _ hA hq hfin
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ eval x q ≠ 0 ∧
    ¬ ∃ s', RatChart.IsRatSheetAt J p q x s'} with hBdef
  choose σ Us W hUs hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨-, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨U', hU', hyU', hsd', hsx, hsec', -⟩ := hsh
    have hD' := isOpen_dom q hU' hsd'
    have hAxD : A *ᵥ x ∈ U' ∩ σ i ⁻¹' {x | eval x q ≠ 0} :=
      ⟨hyU', by simp only [Set.mem_preimage, hsx]; exact hxB.2.2.1⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD' _ hAxD
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => RatChart.ratMap p q (σ i v)) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC hD' (differentiableOn_ratMap_comp p q hsd')).mono hball,
      exists_det_ne_zero hfin hsd' hsec' Metric.isOpen_ball hball ⟨_, Metric.mem_ball_self hr⟩, ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2.2
      (exists_ratSheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hx''B.2.2.1 hne)
  have hBnull : volume ((fun x => A *ᵥ x) '' B) = 0 := by
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
    rintro _ ⟨x, hxB, rfl⟩
    have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
  refine measure_mono_null ?_ (measure_union_null hBnull (volume_image_zero hJ hA hq))
  rintro _ ⟨x, ⟨hxZ, hxs, hnot⟩, rfl⟩
  by_cases hqx : eval x q = 0
  · exact Or.inr ⟨x, ⟨hxZ, hqx⟩, rfl⟩
  · exact Or.inl ⟨x, ⟨hxZ, hxs, hqx, hnot⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
