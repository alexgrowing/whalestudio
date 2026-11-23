import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationSplittingsDiffer

noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct ENNReal NNReal
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open MeasureTheory
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt tensAt_tmul compFin_tensAt tensAt_mul_right)

theorem exists_factor {A K : Type} [AddCommGroup A] [AddCommGroup K] {ev : A →+ K} {ι : K →+ A} [TopologicalSpace A]
    [IsTopologicalAddGroup A] [T2Space A] [TopologicalSpace K] [IsTopologicalAddGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace K] [BorelSpace K]
    (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) (μ : Measure A) [μ.IsAddHaarMeasure] (μ' : Measure K)
    [μ'.IsAddHaarMeasure] {Φ : A → ℂ} (h1 : Continuous Φ) (h2 : HasCompactSupport Φ) (h3 : Φ 0 ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : K → ℂ, Continuous φ → ∫⁻ x, ‖Pm ev ι φ 0 Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ' := by
  have hc := continuous_put hev hι
  have hr : Continuous fun x => Φ (put ev ι x 0) := h1.comp (hc.comp (continuous_id.prodMk continuous_const))
  let w : A → ℝ≥0∞ := fun x => ‖Φ (put ev ι x 0)‖ₑ ^ 2
  have hw : Measurable w := hr.measurable.enorm.pow_const 2
  let ν : Measure K := (μ.withDensity w).map ev
  have hν : ∀ f : K → ℝ≥0∞, Measurable f → ∫⁻ y, f y ∂ν = ∫⁻ x, w x * f (ev x) ∂μ := fun f hf => by
    rw [lintegral_map hf hev.measurable]
    exact lintegral_withDensity_eq_lintegral_mul _ hw (hf.comp hev.measurable)
  have : ν.IsAddLeftInvariant := ⟨fun g => Measure.ext_of_lintegral _ fun f hf => by
    rw [lintegral_map hf (measurable_const_add g), hν (fun a => f (g + a)) (hf.comp (measurable_const_add g)), hν f hf,
      ← lintegral_add_left_eq_self (μ := μ) (fun x => w x * f (ev x)) (ι g)]
    refine lintegral_congr fun x => ?_
    have : put ev ι (ι g + x) 0 = put ev ι x 0 := by simp only [put, map_add, h]; abel
    simp only [w, this, map_add, h]⟩
  have : IsFiniteMeasureOnCompacts ν := ⟨fun S hS => by
    obtain ⟨C, hC⟩ := h1.bounded_above_of_compact_support h2
    obtain ⟨S', hS', hSS⟩ := exists_compact_superset hS
    have hK' : IsCompact ((fun p : A × K => put ev ι p.1 p.2) '' (tsupport Φ ×ˢ S')) := (h2.isCompact.prod hS').image hc
    refine (measure_mono hSS).trans_lt ?_
    rw [← lintegral_indicator_one isOpen_interior.measurableSet,
      hν _ (measurable_one.indicator isOpen_interior.measurableSet)]
    refine (lintegral_mono (g := Set.indicator ((fun p : A × K => put ev ι p.1 p.2) '' (tsupport Φ ×ˢ S'))
      fun _ => ENNReal.ofReal C ^ 2) fun x => ?_).trans_lt ?_
    · by_cases hx : ev x ∈ interior S'
      · by_cases h0 : Φ (put ev ι x 0) = 0
        · simp [w, h0]
        · have hm : x ∈ (fun p : A × K => put ev ι p.1 p.2) '' (tsupport Φ ×ˢ S') := ⟨(put ev ι x 0, ev x),
            ⟨subset_tsupport _ h0, interior_subset hx⟩, by simp only [put_put h, put_self]⟩
          have hb : ‖Φ (put ev ι x 0)‖ₑ ≤ ENNReal.ofReal C := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC _)
          simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hm, Pi.one_apply, mul_one]
          exact pow_le_pow_left' hb 2
      · simp [Set.indicator_of_notMem hx]
    · rw [lintegral_indicator_const hK'.measurableSet]
      exact ENNReal.mul_lt_top (by simp [lt_top_iff_ne_top]) hK'.measure_lt_top⟩
  have e := Measure.isAddLeftInvariant_eq_smul ν μ'
  refine ⟨Measure.addHaarScalarFactor ν μ', fun h0 => ?_, fun φ hφ => ?_⟩
  · rw [h0, zero_smul] at e
    have := hν 1 measurable_one
    rw [e, lintegral_zero_measure] at this
    simp only [Pi.one_apply, mul_one] at this
    refine ((lintegral_pos_iff_support hw).2 ?_).ne this
    rw [show Function.support w = Function.support fun x => Φ (put ev ι x 0) by ext y; simp [w]]
    exact hr.isOpen_support.measure_pos μ ⟨0, by simpa [put] using h3⟩
  · have := hν _ (hφ.measurable.enorm.pow_const 2)
    rw [e, lintegral_smul_measure] at this
    refine Eq.trans (lintegral_congr fun x => ?_) this.symm
    simp only [w, Pm_apply, enorm_mul, mul_pow, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem continuous_tensAt : Continuous (tensAt E v : Ev E v → AE F E) := by
  have : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have e : (tensAt E v : Ev E v → AE F E) = fun y => ∑ i, atPlace v (b.coord i y) • tensAt E v (b i) := by
    funext y
    conv_lhs => rw [← b.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun i _ => smul_tensAt v _ _
  rw [e]
  exact continuous_finsetSum _ fun i _ => ((GlobalTheory.VacAny.continuous_atPlace v).comp
    (IsModuleTopology.continuous_of_linearMap (b.coord i))).smul continuous_const

theorem continuous_liftU {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} {Jv : Matrix β β (Ev E v)}
    (h : J.map (compFin F E v) = Jv) : Continuous (liftU (σ := σ) h) := by
  have : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map continuous_tensAt)
  exact ((Units.continuous_map c1).comp continuous_subtype_val).subtype_mk _

end PositivityTheory.ThKH.Locpair
