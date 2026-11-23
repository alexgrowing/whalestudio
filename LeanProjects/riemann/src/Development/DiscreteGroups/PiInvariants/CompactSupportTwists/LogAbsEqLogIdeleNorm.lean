import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

set_option linter.all false

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem norm_cV_eq (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ := by
  change ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v) (u.1 v)‖ = _
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) _

theorem mult_eq_two (v : InfinitePlace E) : v.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v)]

theorem logAbs_eq_log_ideleNorm (u : (Ad E)ˣ) :
    logAbs (u : Ad E) = Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm u) := by
  have hu : ∀ v, ‖cV v (u : Ad E)‖ ≠ 0 := fun v => norm_ne_zero_iff.2 (u.isUnit.map (cV v)).ne_zero
  have hw : ∀ w, ‖cW w (u : Ad E)‖ ≠ 0 := fun w => norm_ne_zero_iff.2 (u.isUnit.map (cW w)).ne_zero
  have hinf : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm u = ∏ v : InfinitePlace E, ‖cV v (u : Ad E)‖ ^ 2 := by
    change ∏ v : InfinitePlace E, _ = _
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [norm_cV_eq, mult_eq_two]
  have hfin : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm u = ∏ᶠ w : HeightOneSpectrum (𝓞 E), ‖cW w (u : Ad E)‖ := rfl
  have hs : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 E) => ‖cW w (u : Ad E)‖).Finite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finite_mulSupport (E := E) u
  have hsub : (Function.support fun w : HeightOneSpectrum (𝓞 E) => Real.log ‖cW w (u : Ad E)‖) ⊆
      (hs.toFinset : Set (HeightOneSpectrum (𝓞 E))) := fun w hw' => by
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_mulSupport, Function.mem_support] at hw' ⊢
    intro h1
    rw [h1, Real.log_one] at hw'
    exact hw' rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm, MonoidHom.mul_apply, hinf, hfin,
    finprod_eq_prod_of_mulSupport_subset _ (s := hs.toFinset) (fun _ h => hs.mem_toFinset.2 h),
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hu v))
      (Finset.prod_ne_zero_iff.2 fun w _ => hw w),
    Real.log_prod fun v _ => pow_ne_zero _ (hu v), Real.log_prod fun w _ => hw w, logAbs,
    finsum_eq_sum_of_support_subset _ hsub]

theorem continuous_logAbs_det : Continuous fun g : GA E n => logAbs g.val.det := by
  have e : (fun g : GA E n => logAbs g.val.det) =
      fun g => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (Matrix.GeneralLinearGroup.det g)) :=
    funext fun g => logAbs_eq_log_ideleNorm (Matrix.GeneralLinearGroup.det g)
  rw [e]
  exact (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp Matrix.GeneralLinearGroup.continuous_det).log
    fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _

theorem continuous_ldet : Continuous (ldet : H E n 0 → ℝ) :=
  continuous_logAbs_det.comp continuous_fst

theorem continuous_of_mem (π : CuspSub E n) {ψ : Sm E n} (h : ψ ∈ π.V) : Continuous ψ.1 :=
  ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ h).1.level

end DiscreteGroups.T1.G
