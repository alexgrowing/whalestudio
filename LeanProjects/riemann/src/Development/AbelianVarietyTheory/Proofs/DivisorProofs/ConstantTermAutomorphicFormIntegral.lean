import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

def invM (y : Lie E a) : Lie E a := toL (Matrix.of y)⁻¹

omit [IsTotallyComplex E] in

theorem contDiffOn_invM : ContDiffOn ℝ ∞ (invM (E := E) (a := a)) (invSet E a) := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Lie E a => Ring.inverse (Matrix.of y).det) (invSet E a) := fun y hy => by
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun y : Lie E a => (Matrix.of y).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    have h3 : ContDiff ℝ ∞ fun y : Lie E a => (Function.update y j (Pi.single i 1) : Lie E a) := by
      refine contDiff_pi.2 fun k => ?_
      by_cases h : k = j
      · subst h; simpa using contDiff_const
      · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
    exact contDiff_det.comp h3
  exact h1.mul h2.contDiffOn

theorem continuous_infGL : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem continuousOn_chart {φ : GA E a → ℂ} (hφ : Continuous φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ p.1 p.2) (Set.univ ×ˢ invSet E a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hu : Continuous fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) =>
      (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_snd.comp continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous
      (f := fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) => p.1.2)
      (continuous_snd.comp continuous_subtype_val) fun p => p.2.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  refine (hφ.comp ((continuous_fst.comp continuous_subtype_val).mul (continuous_infGL.comp hu))).congr fun p => ?_
  exact (chart_val φ p.1.1 (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)))).symm

omit [IsTotallyComplex E] in

def coef (i : Fin (Module.finrank ℝ (Lie E a))) (y : Lie E a) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L lmul (invM y)

omit [IsTotallyComplex E] in

theorem contDiffOn_coef (i : Fin (Module.finrank ℝ (Lie E a))) : ContDiffOn ℝ ∞ (coef i) (invSet E a) := by
  refine contDiffOn_clm_apply.2 fun Y => ?_
  exact (Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L
    rmul Y).contDiff.comp_contDiffOn contDiffOn_invM

theorem fderiv_chart (φ : Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart φ.1 g) y = ∑ i, chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g y • coef i y := by
  ext Y
  have e : Y = rmul (lmul (invM y) Y) y := by
    change Matrix.of Y = Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of Y)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hy)]
  have e2 : ∀ X, rmul X y = lmul y X := fun _ => rfl
  conv_lhs => rw [e, e2, ← (Module.finBasis ℝ (Lie E a)).sum_repr (lmul (invM y) Y)]
  rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← e2, ← chart_lieD φ.2 _ g hy, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm,
    Complex.real_smul]
  rfl

def Good (φ : Sm E a) : Prop := (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}

theorem Good.lie {φ : Sm E a} (h : Good φ) (X : Lie E a) : Good (lie E a X φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
      funext x; simp only [chart, mul_assoc, h.1]
    simp only [lie_apply, lieD, e]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)
    have e := LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : rt E a (finGL E a k) φ = φ := hk
    simp only [Module.End.mul_apply, hk'] at e
    exact e.symm

omit [IsTotallyComplex E] in

theorem exists_bound {r : ℕ} {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V} {S : Set (Lie E a)}
    (hS : IsCompact S) (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ S))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) :
    ∃ C, ∀ (x : BlockIx a r → Ad E), ∀ y ∈ S, ‖Ψ (unip x * g) y‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (f := fun p : (BlockIx a r → Ad E) × Lie E a => Ψ (unip p.1 * g) p.2)
    (hc.comp (((CuspidalL2GL.continuous_unip.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun p hp => ⟨trivial, hp.2⟩)
  refine ⟨C, fun x y hy => ?_⟩
  obtain ⟨_, ⟨z, rfl⟩, hk⟩ := hcov x
  have := hC (_, y) ⟨hk, hy⟩
  simp only [unip_add, mul_assoc] at this
  exact (congrArg (fun f => ‖f y‖) ((congrArg (fun u => Ψ (u * _)) (unip_algebraMap z)).trans (hl _ _))).symm.trans_le
    this

theorem Good.chart_left {φ : Sm E a} (h : Good φ) (γ : GL (Fin a) E) (g : GA E a) :
    chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
  funext x; simp only [chart, mul_assoc, h.1]

theorem Good.continuousOn_chart {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ.1 p.1 p.2) (Set.univ ×ˢ invSet E a) :=
  ConstTermSmooth.continuousOn_chart (ContAut.continuous_of_isOpen_stab E a φ h.2)

theorem Good.continuousOn_fderiv {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => fderiv ℝ (chart φ.1 p.1) p.2) (Set.univ ×ˢ invSet E a) := by
  refine ContinuousOn.congr ?_ fun p hp => fderiv_chart φ p.1 hp.2
  exact continuousOn_finset_sum _ fun i _ => (h.lie _).continuousOn_chart.smul
    ((contDiffOn_coef i).continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2)

section Integral

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
  (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν]

omit [IsTotallyComplex E] in

theorem integrable_unip {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V}
    (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ invSet E a))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x => Ψ (unip x * g) y) ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  obtain ⟨C, hC⟩ := exists_bound (r := r) (isCompact_singleton (x := y))
    (hc.mono (Set.prod_mono_right (Set.singleton_subset_iff.2 hy))) hl g
  have hf : Continuous fun x : BlockIx a r → Ad E => Ψ (unip x * g) y :=
    hc.comp_continuous ((CuspidalL2GL.continuous_unip.mul continuous_const).prodMk continuous_const) fun _ => ⟨trivial, hy⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun x => hC x y rfl)

omit [BorelSpace (BlockIx a r → Ad E)] [IsFiniteMeasure ν] in

theorem chart_integral (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun g => ∫ x, φ (unip x * g) ∂ν) g = fun y => ∫ x, chart φ (unip x * g) y ∂ν := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, integral_zero]

theorem Good.hasFDerivAt {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    HasFDerivAt (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (∫ x, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν) y := by
  rw [chart_integral]
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hl : ∀ γ g, (fun y => fderiv ℝ (chart φ.1 (ratGL E a γ * g)) y) = fun y => fderiv ℝ (chart φ.1 g) y :=
    fun γ g => by rw [h.chart_left]
  obtain ⟨C, hC⟩ := exists_bound (r := r) (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) hS
    (h.continuousOn_fderiv.mono (Set.prod_mono_right hSU)) hl g
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz =>
      (integrable_unip ν h.continuousOn_chart h.chart_left g hz).1)
    (integrable_unip ν h.continuousOn_chart h.chart_left g hy)
    (integrable_unip ν (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv hl g hy).1
    (.of_forall hC) (integrable_const C) (.of_forall fun x z hz => ?_)
  exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt

theorem Good.fderiv_integral {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) y = ∑ i,
      chart (fun g => ∫ x, (CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (unip x * g) ∂ν) g y • coef i y := by
  rw [(h.hasFDerivAt ν g hy).fderiv]
  simp only [fderiv_chart φ _ hy, chart_integral]
  rw [integral_finset_sum _ fun i _ =>
    (integrable_unip ν (h.lie _).continuousOn_chart (h.lie _).chart_left g hy).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

theorem contDiffOn_integral (g : GA E a) (n : ℕ) : ∀ φ : Sm E a, Good φ →
    ContDiffOn ℝ n (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (invSet E a) := by
  induction n with
  | zero =>
    intro φ h
    exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt ν g hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro φ h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (h.hasFDerivAt ν g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun y hy => h.fderiv_integral ν g hy
    exact ContDiffOn.sum fun i _ => (ih _ (h.lie _)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))

end Integral

theorem constTerm_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a),
      lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hl ho
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  have h : Good φ := ⟨hl, ho⟩
  refine ⟨fun g => contDiffOn_infty.2 fun n => contDiffOn_integral _ g n φ h, fun X g => ?_⟩
  rw [lieD, (h.hasFDerivAt (μ.restrict 𝓕) g (y := oneL E a) isUnit_one).fderiv, ContinuousLinearMap.integral_apply
    (integrable_unip _ (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv
      (fun γ g => by rw [h.chart_left]) g (y := oneL E a) isUnit_one)]
  rfl

end GlobalTheory.ConstTermSmooth
