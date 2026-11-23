import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal Pointwise

variable {D : D7}

theorem borel_Mx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  aedisjoint := by
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

theorem lintegral_resS {S A B T : HSp D} (o : OrthDec S A B) (μ : Measure (WO S T)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (WO S T)) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (μA : Measure (WO A T)) (μB : Measure (WO B T))
    [μA.IsAddHaarMeasure] [μB.IsAddHaarMeasure] (FA : Set (WO A T)) (FB : Set (WO B T))
    (hA : IsAddFundamentalDomain (ratL T A) FA μA) (hB : IsAddFundamentalDomain (ratL T B) FB μB) :
    ∃ c : ℝ≥0, ∀ Φ : WO A T × WO B T → ℝ≥0∞, (∀ γ ∈ ratL T S, ∀ x, Φ (o.resS T (γ + x)) = Φ (o.resS T x)) →
      ∫⁻ x in 𝓕, Φ (o.resS T x) ∂μ = c • ∫⁻ y, Φ y ∂((μA.restrict FA).prod (μB.restrict FB)) := by
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  haveI : Countable (ratL T S) :=
    (TopologicalSpace.separableSpace_iff_countable.1 inferInstance : Countable (ratMx D T.rank S.rank))
  haveI : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun _ => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  let e : WO S T ≃ₜ (WO A T × WO B T) :=
    { (o.resS T).toEquiv with continuous_toFun := o.continuous_resS T, continuous_invFun := o.continuous_resS_symm T }
  let em := e.toMeasurableEquiv
  haveI : (μ.map em).IsAddHaarMeasure :=
    (o.resS T).isAddHaarMeasure_map μ (o.continuous_resS T) (o.continuous_resS_symm T)
  obtain ⟨c, hmeq⟩ : ∃ c : ℝ≥0, μ.map em = c • μA.prod μB :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map em) (μA.prod μB)⟩
  refine ⟨c, fun Φ hper => ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving em μ (μA.prod μB) :=
    ⟨em.measurable, by rw [hmeq]; exact Measure.smul_absolutelyContinuous⟩
  have hprod := isAddFundamentalDomain_prod hA hB
  have hmem : ∀ g : (ratL T A).prod (ratL T B), (o.resS T).symm (g : WO A T × WO B T) ∈ ratL T S := fun g => by
    rw [o.mem_ratL_resS, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 g.2
  have hP : IsAddFundamentalDomain (ratL T S) (em ⁻¹' (FA ×ˢ FB)) μ := by
    refine hprod.preimage_of_equiv hqmp (e := fun g => ⟨_, hmem g⟩) ⟨fun g g' h => ?_, fun h => ?_⟩ fun g x => ?_
    · exact Subtype.ext ((o.resS T).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resS T h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resS T h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resS T).symm_apply_apply h
    · change o.resS T ((o.resS T).symm (g : WO A T × WO B T) + x) = (g : WO A T × WO B T) + o.resS T x
      rw [map_add, AddEquiv.apply_symm_apply]
  rw [h𝓕.setLIntegral_eq hP (fun x => Φ (o.resS T x)) (fun g x => hper g g.2 x)]
  change ∫⁻ x in em ⁻¹' (FA ×ˢ FB), Φ (em x) ∂μ = _
  rw [← lintegral_map_equiv _ em, ← em.restrict_map, hmeq, Measure.restrict_smul, lintegral_smul_measure,
    Measure.prod_restrict]

end GlobalTheory.WeilSliceUnit

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal

variable {D : D7}

theorem enorm_sq_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ γ ∈ ratL T S, ∀ x, ‖f (γ + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
  rintro _ ⟨g, rfl⟩ x
  have h : ‖f (ratW T S g + x)‖ = ‖f x‖ := by rw [hf.quasi, norm_mul, hψ.1.2.1, one_mul]
  show ‖f (ratW T S g + x)‖ₑ ^ 2 = _
  rw [← ofReal_norm, ← ofReal_norm, h]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  intro D ψ S A B T o μ 𝓕 hμ h𝓕 f hf
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  obtain ⟨μA, FA, hA⟩ := exists_isCovolOne D T.rank A.rank
  obtain ⟨μB, FB, hB⟩ := exists_isCovolOne D T.rank B.rank
  haveI := hA.1
  haveI := hB.1
  have hFA : IsAddFundamentalDomain (ratL T A) FA μA := hA.2.1
  have hFB : IsAddFundamentalDomain (ratL T B) FB μB := hB.2.1
  obtain ⟨c, hc⟩ := lintegral_resS o μ 𝓕 h𝓕 μA μB FA FB hFA hFB
  have hslice := GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf
  have hΦ0 : Measurable fun y : WO A T × WO B T => ‖f ((o.resS T).symm y)‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hf.cont.comp (o.continuous_resS_symm T)))).measurable
  have e0 : ∀ hψ : IsStdChar D ψ (-1), ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ = c • ∫⁻ y, ‖f ((o.resS T).symm y)‖ₑ ^ 2
      ∂((μA.restrict FA).prod (μB.restrict FB)) := by
    intro hψ
    have h := hc (fun y => ‖f ((o.resS T).symm y)‖ₑ ^ 2) (fun γ hγ x => by
      simp only [AddEquiv.symm_apply_apply]; exact enorm_sq_periodic hψ hf γ hγ x)
    simpa only [AddEquiv.symm_apply_apply] using h
  refine ⟨fun χ χ' om hW p => ?_, fun χ χ' om hW p => ?_⟩
  · have hψ := hW.std
    have hF := hslice.1 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod_symm _ hΦ1.aemeasurable, lintegral_prod_symm _ hΦ0.aemeasurable]
    refine lintegral_congr fun v => ?_
    show ∫⁻ u in FA, ‖om p (fun u => f ((o.resS T).symm (u, v))) u‖ₑ ^ 2 ∂μA =
      ∫⁻ u in FA, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μA
    exact hW.om_unit μA FA hA.1 hFA p (fun u => f ((o.resS T).symm (u, v))) (hbox.1 v)
  · have hψ := hW.std
    have hF := hslice.2 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod _ hΦ1.aemeasurable, lintegral_prod _ hΦ0.aemeasurable]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v in FB, ‖om p (fun v => f ((o.resS T).symm (u, v))) v‖ₑ ^ 2 ∂μB =
      ∫⁻ v in FB, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μB
    exact hW.om_unit μB FB hB.1 hFB p (fun v => f ((o.resS T).symm (u, v))) (hbox.2 u)

end GlobalTheory.WeilSliceUnit

end
