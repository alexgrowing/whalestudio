import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenHg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenPoly

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_inf_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : Mx F E d.m d.n) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv) (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, _root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
  exact (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k R X (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X)).1 rfl w
theorem mem_fock_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∃ P : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ,
      ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  set Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ)
      (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2
  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X))) * gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [_root_.PositivityTheory.SiegelWeilFormula.KFock.cmb_crd_k]
    rw [e1, ← hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.crd_inf_eq_k R L hL X]
    rfl
  have hfjn : ∀ u y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  let Φv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals
  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  let ψ : (Fin N → ℂ) → _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.poly_mem_k R P hSB)
  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0
    · have hz : ∀ i, gg i (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [Set.indicator_of_notMem this, mul_zero]
    · have hmemK : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [Set.indicator_of_mem (show _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∈ {y | Φv y = Φv (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)} from rfl), mul_one]
      · intro c _ hne
        have : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [Set.indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
