import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem zeroLocus_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J =
      GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J := rfl

theorem linVal_eq (u x : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.linVal u x = GroundTheory.Heights₂.Heights.linEval u x := rfl

theorem smoothNear_iff (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SmoothNear S f ↔ GroundTheory.Heights₂.Heights.SmoothNear S f :=
  Iff.rfl

theorem withFirst_eq {e : ℕ} (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.withFirst f ψ = Matrix.vecCons f ψ := rfl

theorem fibre_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (w : Fin d → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w =
      GroundTheory.Heights₂.Heights.ComplexSets.fibre J A w := rfl

theorem aeval_linForm_eq_projHom (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (aeval (R := ℂ) fun i : Fin d => Ideal.Quotient.mk J (linForm (A i))) =
      GroundTheory.Heights₂.Heights.ComplexSets.projHom J A := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
    GroundTheory.Heights₂.Heights.ComplexSets.linPoly, linForm]

theorem injective_projHom_of_finite {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d)
    (hfin : (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.Finite) :
    Function.Injective (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A) := by
  have := hJ.isPrime
  let f := (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom
  let P := RingHom.ker f
  let g : MvPolynomial (Fin d) ℂ ⧸ P →+* MvPolynomial (Fin n) ℂ ⧸ J := RingHom.kerLift f
  have hgf : g.comp (Ideal.Quotient.mk P) = f :=
    RingHom.ext fun a => RingHom.kerLift_mk f a
  have hg_fin : g.Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk P) (by rw [hgf]; exact hfin)
  let := g.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ ⧸ P) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hg_fin.to_isIntegral⟩
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ _)) fun _ _ hpq =>
      Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ ⧸ P) hpq
  rw [hJ.dim] at h1
  have hd : ringKrullDim (MvPolynomial (Fin d) ℂ) = (d : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have haP : a ∈ P := ha
  have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr haP)
  rw [hd] at h2
  have h3 := (add_le_add_left h1 1).trans h2
  have h4 : d + 1 ≤ d := by exact_mod_cast h3
  omega

theorem isFiniteProj_iff {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A ↔
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A := by
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj
  rw [aeval_linForm_eq_projHom]
  exact ⟨fun h => ⟨injective_projHom_of_finite hJ h, h⟩, fun h => h.finite⟩

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem isSheetAt_of_isGraphChart {σ : (Fin d → ℂ) → Fin n → ℂ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ) :
    GroundTheory.Heights₂.Heights.IsSheetAt J A x σ := by
  obtain ⟨hx, U, V, hU, hxU, hV, han, hbij, hsec⟩ := h
  obtain ⟨w, hwV, hw⟩ := hbij.surjOn ⟨hx, hxU⟩
  have hAx : A *ᵥ x = w := by rw [← hw]; exact hsec w hwV
  refine ⟨V, hV, by rw [hAx]; exact hwV, han.differentiableOn, by rw [hAx, hw],
    fun y hy => ⟨hsec y hy, (hbij.mapsTo hy).1⟩, U, hU.mem_nhds hxU, ?_⟩
  rintro x' ⟨hx'Z, hx'U⟩ _
  obtain ⟨w', hw'V, hw'⟩ := hbij.surjOn ⟨hx'Z, hx'U⟩
  have hA' : A *ᵥ x' = w' := by rw [← hw']; exact hsec w' hw'V
  rw [hA', hw']

theorem isGraphChart_of_isSheetAt {s : (Fin d → ℂ) → Fin n → ℂ}
    (h : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x s := by
  obtain ⟨W, hW, hAxW, hsd, hsx, hsec, N, hN, hloc⟩ := h
  obtain ⟨U0, hU0N, hU0, hxU0⟩ := mem_nhds_iff.mp hN
  let V := W ∩ s ⁻¹' U0
  have hVo : IsOpen V := hsd.continuousOn.isOpen_inter_preimage hW hU0
  have hAxV : A *ᵥ x ∈ V := ⟨hAxW, by show s (A *ᵥ x) ∈ U0; rw [hsx]; exact hxU0⟩
  have hxZ : x ∈ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J := by
    have := (hsec _ hAxW).2
    rw [hsx] at this
    exact this
  let U := U0 ∩ (fun z => A *ᵥ z) ⁻¹' V
  have hUo : IsOpen U :=
    hU0.inter (hVo.preimage (Continuous.matrix_mulVec continuous_const continuous_id))
  refine ⟨hxZ, U, V, hUo, ⟨hxU0, hAxV⟩, hVo,
    analyticOnNhd_of_differentiableOn hVo (hsd.mono Set.inter_subset_left), ⟨?_, ?_, ?_⟩,
    fun w hw => (hsec w hw.1).1⟩
  · intro y hy
    refine ⟨(hsec y hy.1).2, hy.2, ?_⟩
    show A *ᵥ s y ∈ V
    rw [(hsec y hy.1).1]
    exact hy
  · intro y hy y' hy' hyy'
    have := congrArg (fun z => A *ᵥ z) hyy'
    rwa [(hsec y hy.1).1, (hsec y' hy'.1).1] at this
  · rintro x' ⟨hx'Z, hx'U0, hx'V⟩
    exact ⟨A *ᵥ x', hx'V, (hloc x' ⟨hx'Z, hU0N hx'U0⟩ hx'V.1).symm⟩

theorem exists_graphChart_iff :
    (∃ σ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ) ↔
      ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s :=
  ⟨fun ⟨σ, h⟩ => ⟨σ, isSheetAt_of_isGraphChart h⟩,
    fun ⟨s, h⟩ => ⟨s, isGraphChart_of_isSheetAt h⟩⟩

theorem graphChart_eventuallyEq_sheet {σ s : (Fin d → ℂ) → Fin n → ℂ}
    (hσ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ)
    (hs : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) : σ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨-, U, V, hU, hxU, -, -, hbij, hsec⟩ := hσ
  obtain ⟨W, hW, hAxW, hsd, hsx, hssec, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := hsd.continuousOn.continuousAt (hW.mem_nhds hAxW)
  have h1 : ∀ᶠ y in 𝓝 (A *ᵥ x), s y ∈ U :=
    hcont.preimage_mem_nhds (by rw [hsx]; exact hU.mem_nhds hxU)
  have h2 : ∀ᶠ y in 𝓝 (A *ᵥ x), y ∈ W := hW.mem_nhds hAxW
  filter_upwards [h1, h2] with y hyU hyW
  obtain ⟨w, hwV, hw⟩ := hbij.surjOn ⟨(hssec y hyW).2, hyU⟩
  have hwy : w = y := by rw [← hsec w hwV, hw, (hssec y hyW).1]
  rw [hwy] at hw
  exact hw

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]

theorem maDens_graphChart_eq_sheet {σ s : (Fin d → ℂ) → Fin n → ℂ}
    (hσ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ)
    (hs : GroundTheory.Heights₂.Heights.IsSheetAt J A x s) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (A *ᵥ x) :=
  maDens_congr_of_eventuallyEq fun k => (graphChart_eventuallyEq_sheet hσ hs).fun_comp (φ k)

open Classical in

theorem sheetDens_eq (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens J A φ x =
      if h : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s then
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (A *ᵥ x) else 0 := by
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens
  by_cases h : ∃ σ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGraphChart J A x σ
  · have h' : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s := exists_graphChart_iff.mp h
    rw [dif_pos h, dif_pos h']
    exact maDens_graphChart_eq_sheet h.choose_spec h'.choose_spec φ
  · have h' : ¬ ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s :=
      fun h' => h (exists_graphChart_iff.mpr h')
    rw [dif_neg h, dif_neg h']

theorem fibreSum_eq_chartDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (w : Fin d → ℂ) :
    ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w,
        g x * GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens J A φ x =
      GroundTheory.Heights₂.Heights.chartDens J A g φ w := by
  unfold GroundTheory.Heights₂.Heights.chartDens GroundTheory.Heights₂.Heights.sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  rw [sheetDens_eq, hx.2]
  by_cases h : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, mul_zero]

theorem fibreAbsSum_eq_chartAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (w : Fin d → ℂ) :
    ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w,
        |g x * GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.sheetDens J A φ x| =
      GroundTheory.Heights₂.Heights.chartAbsDens J A g φ w := by
  unfold GroundTheory.Heights₂.Heights.chartAbsDens GroundTheory.Heights₂.Heights.sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  rw [sheetDens_eq, hx.2]
  by_cases h : ∃ s, GroundTheory.Heights₂.Heights.IsSheetAt J A x s
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, mul_zero, abs_zero]

theorem projInt_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.projInt J A g φ =
      GroundTheory.Heights₂.Heights.chartInt J A g φ := by
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.projInt GroundTheory.Heights₂.Heights.chartInt
  simp only [fibreSum_eq_chartDens]

theorem projIntegrable_iff (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjIntegrable J A g φ ↔
      Integrable (GroundTheory.Heights₂.Heights.chartAbsDens J A g φ) := by
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProjIntegrable
  simp only [fibreAbsSum_eq_chartAbsDens]

theorem choose_congr {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a)
    (hq : ∃ a, q a) : hp.choose = hq.choose := by
  subst hpq
  rfl

theorem varIntegral_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J d) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.varIntegral J g φ =
      GroundTheory.Heights₂.Heights.varInt J d g φ := by
  have hp : (fun A : Matrix (Fin d) (Fin n) ℂ =>
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A) =
      fun A => GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A :=
    funext fun A => propext (isFiniteProj_iff hJ)
  unfold GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.varIntegral GroundTheory.Heights₂.Heights.varInt
  by_cases h : ∃ A : Matrix (Fin d) (Fin n) ℂ,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A
  · have h' : ∃ A : Matrix (Fin d) (Fin n) ℂ,
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A := by
      obtain ⟨A, hA⟩ := h
      exact ⟨A, (isFiniteProj_iff hJ).mpr hA⟩
    rw [dif_pos h, dif_pos h', projInt_eq, choose_congr hp h' h]
  · have h' : ¬ ∃ A : Matrix (Fin d) (Fin n) ℂ,
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsFiniteProj J A := by
      rintro ⟨A, hA⟩
      exact h ⟨A, (isFiniteProj_iff hJ).mp hA⟩
    rw [dif_neg h, dif_neg h']

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
