import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldDCUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.ComplexDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.Slab

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section DC

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem countable_of_le (Γ S : Subgroup G) [Countable Γ] (h : S ≤ Γ) : Countable S :=
  (Subgroup.inclusion_injective h).countable

theorem countable_of_sub (Γ : Subgroup G) [Countable Γ] (E : Set G) (h : E ⊆ (Γ : Set G)) : Countable E := by
  haveI : Countable (Γ : Set G) := ‹Countable Γ›
  exact ((Set.countable_coe_iff.mp this).mono h).to_subtype

theorem dcSingleE (Γ S S' : Subgroup G) [Countable Γ] (hS : S ≤ Γ) (hS' : S' ≤ Γ)
    (D' : Set G) (hD' : IsRightTransversal Γ S' D')
    (R : Set G) (hR : IsDoubleTransversal Γ S S' R)
    (Fs : G → Set G) (hFs : ∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ)
    (F : Set G) (hF : IsFundamentalDomain S F μ)
    (f h : G → ℝ≥0∞) (hfm : Measurable f) (hhm : Measurable h)
    (hf : ∀ s ∈ S, ∀ y, f (s * y) = f y) (hh : ∀ s ∈ S', ∀ y, h (s * y) = h y) :
    ∫⁻ x in F, f x * ∑' δ : D', h ((δ : G) * x) ∂μ = ∑' r : R, ∫⁻ x in Fs r, f x * h ((r : G)⁻¹ * x) ∂μ := by
  have hEx : ∀ r : G, ∃ E : Set G, IsRightTransversal S (stab S S' r) E :=
    fun r => PI.FoldDCUnfold.W.translation_exists G S (stab S S' r) inf_le_left
  choose E hE using hEx
  obtain ⟨hinj, hT⟩ := PI.FoldDCUnfold.W.double_coset_translation G Γ S S' hS hS' R hR E (fun r _ => hE r)
  have : Countable S := countable_of_le Γ S hS
  have hRc : Countable R := countable_of_sub Γ R hR.1
  have hEc : ∀ r : G, Countable (E r) := fun r => countable_of_sub Γ (E r) (fun x hx => hS ((hE r).1 hx))
  have hφm : ∀ r : G, Measurable (fun y : G => f y * h (r⁻¹ * y)) :=
    fun r => hfm.mul (hhm.comp (measurable_const_mul _))
  have hφi : ∀ r : G, ∀ s ∈ stab S S' r, ∀ y : G,
      f (s * y) * h (r⁻¹ * (s * y)) = f y * h (r⁻¹ * y) := by
    intro r s hs y
    rw [mem_stab] at hs
    rw [hf s hs.1, show r⁻¹ * (s * y) = (r⁻¹ * s * r) * (r⁻¹ * y) by group, hh _ hs.2]
  have hpt : ∀ x : G, f x * ∑' δ : D', h ((δ : G) * x) =
      ∑' r : R, ∑' t : E (r : G), f ((t : G) * x) * h ((r : G)⁻¹ * ((t : G) * x)) := by
    intro x
    have e1 := PI.FoldDCUnfold.W.translation_independent G Γ S' _ D' hT hD' 1 Γ.one_mem (fun y => h (y * x))
      (fun s hs y => by simp only [mul_assoc]; exact hh s hs (y * x))
    simp only [mul_one] at e1
    rw [← e1, ← (Equiv.ofInjective _ hinj).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun t => ?_
    have ht : (t : G) ∈ S := (hE (r : G)).1 t.2
    simp only [Equiv.ofInjective_apply, mul_assoc, hf _ ht]
  calc ∫⁻ x in F, f x * ∑' δ : D', h ((δ : G) * x) ∂μ
      = ∫⁻ x in F, ∑' r : R, ∑' t : E (r : G), f ((t : G) * x) * h ((r : G)⁻¹ * ((t : G) * x)) ∂μ :=
        lintegral_congr hpt
    _ = ∑' r : R, ∫⁻ x in F, ∑' t : E (r : G), f ((t : G) * x) * h ((r : G)⁻¹ * ((t : G) * x)) ∂μ := by
        refine lintegral_tsum fun r => ?_
        have := hEc (r : G)
        exact (Measurable.ennreal_tsum fun t => (hφm (r : G)).comp (measurable_const_mul _)).aemeasurable
    _ = ∑' r : R, ∫⁻ x in Fs r, f x * h ((r : G)⁻¹ * x) ∂μ := by
        refine tsum_congr fun r => ?_
        exact lintegralTransversalSum G μ S (stab S S' r) inf_le_left (Fs r) (hFs r r.2) F hF (E r) (hE r) _
          (hφm r) (hφi r)

end DC

open PI.PoincareSeriesInner.W in

theorem double_coset_single_unfolding : Formalism.L2.SG.TermOp.KExpCut.DCSingle := by
  intro G _ _ _ μ _ _ Γ S S' _ hS hS' D' hD' R hR Fs hFs F hF f g hfm hgm hfi hgi hfin hsum
  set ψ : G → ℂ := fun x => conj (g x) with hψdef
  have hψm : Measurable ψ := Complex.continuous_conj.measurable.comp hgm
  have hψi : ∀ s ∈ S', ∀ y, ψ (s * y) = ψ y := fun s hs y => by simp only [ψ, hgi s hs y]
  have hψn : ∀ x, ‖ψ x‖ₑ = ‖g x‖ₑ := fun x => by
    rw [← ofReal_norm, ← ofReal_norm]; simp only [ψ, Complex.norm_conj]
  have hconj : ∀ x, conj (∑' δ : D', g ((δ : G) * x)) = poinc D' ψ x := fun x => by
    simp only [poinc, ψ, starRingEnd_apply]; exact tsum_star
  have hgs : ∀ x, ∑' δ : D', ‖ψ ((δ : G) * x)‖ₑ ≠ ⊤ := fun x => by
    simp_rw [hψn]
    have := (hsum x).toNNReal
    rw [← ENNReal.tsum_coe_ne_top_iff_summable] at this
    refine ne_of_eq_of_ne (tsum_congr fun δ => ?_) this
    rw [← ofReal_norm]
    rfl
  obtain ⟨u, hu⟩ : ∃ u : Fin 4 → G → ℝ≥0∞, u = fun k x => part k (f x) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → G → ℝ≥0∞, w = fun k x => part k (ψ x) := ⟨_, rfl⟩
  have hum : ∀ k, Measurable (u k) := fun k => by rw [hu]; exact (measurable_part k).comp hfm
  have hwm : ∀ k, Measurable (w k) := fun k => by rw [hw]; exact (measurable_part k).comp hψm
  have hui : ∀ k, ∀ s ∈ S, ∀ y : G, u k (s * y) = u k y := fun k s hs y => by
    rw [hu]; simp only [hfi s hs y]
  have hwi : ∀ k, ∀ s ∈ S', ∀ y : G, w k (s * y) = w k y := fun k s hs y => by
    rw [hw]; simp only [hψi s hs y]
  have hut : ∀ k x, u k x ≠ ⊤ := fun k x => by rw [hu]; exact part_ne_top _ _
  have hwt : ∀ k x, w k x ≠ ⊤ := fun k x => by rw [hw]; exact part_ne_top _ _
  have hule : ∀ k x, u k x ≤ ‖f x‖ₑ := fun k x => by rw [hu]; exact part_le _ _
  have hwle : ∀ k x, w k x ≤ ‖g x‖ₑ := fun k x => by rw [hw, ← hψn]; exact part_le _ _
  have hWle : ∀ k x, ∑' δ : D', w k ((δ : G) * x) ≤ ∑' δ : D', ‖ψ ((δ : G) * x)‖ₑ := fun k x =>
    ENNReal.tsum_le_tsum fun δ => by rw [hw]; exact part_le _ _
  have hWt : ∀ k x, ∑' δ : D', w k ((δ : G) * x) ≠ ⊤ := fun k x =>
    ne_top_of_le_ne_top (hgs x) (hWle k x)
  have hD'c : Countable D' := countable_of_sub Γ D' hD'.1
  have hWm : ∀ k, Measurable fun x => ∑' δ : D', w k ((δ : G) * x) :=
    fun k => Measurable.ennreal_tsum fun δ => (hwm k).comp (measurable_const_mul _)
  have hsf : ∀ x, f x = ∑ k, cf k * ((u k x).toReal : ℂ) := fun x => by rw [hu]; exact split (f x)
  have hsψ : ∀ x, ψ x = ∑ k, cf k * ((w k x).toReal : ℂ) := fun x => by rw [hw]; exact split (ψ x)
  have hprod : ∀ x, f x * poinc D' ψ x = ∑ k, ∑ l, cf k * cf l *
      (((u k x * (∑' δ : D', w l ((δ : G) * x)))).toReal : ℂ) := by
    intro x
    rw [hsf x, poinc_split D' w ψ hsψ hWt x, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  have hprodR : ∀ (r x : G), f x * ψ (r⁻¹ * x) = ∑ k, ∑ l, cf k * cf l *
      (((u k x * w l (r⁻¹ * x))).toReal : ℂ) := by
    intro r x
    rw [hsf x, hsψ (r⁻¹ * x), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  have hDC : ∀ k l, (∫⁻ x in F, u k x * ∑' δ : D', w l ((δ : G) * x) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ := fun k l =>
    dcSingleE μ Γ S S' hS hS' D' hD' R hR Fs hFs F hF (u k) (w l) (hum k) (hwm l) (hui k) (hwi l)
  have hSkl : ∀ k l, ∑' r : R, ∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ ≠ ⊤ := fun k l =>
    ne_top_of_le_ne_top hfin.ne (ENNReal.tsum_le_tsum fun r => lintegral_mono fun x =>
      mul_le_mul' (hule k x) (hwle l _))
  have hXkl : ∀ k l, (∫⁻ x in F, u k x * ∑' δ : D', w l ((δ : G) * x) ∂μ) ≠ ⊤ := fun k l => by
    rw [hDC k l]; exact hSkl k l
  have hIkl : ∀ k l (r : R), ∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ ≠ ⊤ :=
    fun k l r => ENNReal.ne_top_of_tsum_ne_top (hSkl k l) r
  have hL := fun k l => toReal_int (ν := μ.restrict F)
    (f := fun x => u k x * ∑' δ : D', w l ((δ : G) * x))
    (((hum k).mul (hWm l)).aemeasurable) (hXkl k l) (fun x => ENNReal.mul_ne_top (hut k x) (hWt l x))
  have hR' := fun k l (r : R) => toReal_int (ν := μ.restrict (Fs r))
    (f := fun x => u k x * w l ((r : G)⁻¹ * x))
    (((hum k).mul ((hwm l).comp (measurable_const_mul _))).aemeasurable) (hIkl k l r)
    (fun x => ENNReal.mul_ne_top (hut k x) (hwt l _))
  have hfun : (fun x => f x * conj (∑' δ : D', g ((δ : G) * x))) = fun x => ∑ k, ∑ l, cf k * cf l *
      (((u k x * (∑' δ : D', w l ((δ : G) * x)))).toReal : ℂ) := by
    funext x; rw [hconj x]; exact hprod x
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hfun]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hL k l).1.const_mul _
  · have hLHS : (∫ x in F, f x * conj (∑' δ : D', g ((δ : G) * x)) ∂μ) = ∑ k, ∑ l, cf k * cf l *
        ∑' r : R, (((∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ) := by
      rw [hfun, integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun l _ => ?_
          rw [integral_const_mul, (hL k l).2, hDC k l,
            ENNReal.tsum_toReal_eq (hIkl k l), Complex.ofReal_tsum]
        · intro l _; exact (hL k l).1.const_mul _
      · intro k _; exact integrable_finsetSum _ fun l _ => (hL k l).1.const_mul _
    have hRHS : ∀ r : R, (∫ x in Fs r, f x * conj (g ((r : G)⁻¹ * x)) ∂μ) = ∑ k, ∑ l, cf k * cf l *
        (((∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ) := by
      intro r
      have e : (fun x => f x * conj (g ((r : G)⁻¹ * x))) = fun x => f x * ψ ((r : G)⁻¹ * x) := rfl
      rw [e]
      simp_rw [hprodR]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun l _ => ?_
          rw [integral_const_mul]
          exact congrArg _ (hR' k l r).2
        · intro l _; exact (hR' k l r).1.const_mul _
      · intro k _; exact integrable_finsetSum _ fun l _ => (hR' k l r).1.const_mul _
    have hsum' : ∀ k l, Summable fun r : R =>
        (((∫⁻ x in Fs r, u k x * w l ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ) := fun k l =>
      (Complex.summable_ofReal).2 (ENNReal.summable_toReal (hSkl k l))
    rw [hLHS, tsum_congr hRHS, Summable.tsum_finsetSum
      (fun k _ => summable_sum fun l _ => (hsum' k l).mul_left _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Summable.tsum_finsetSum (fun l _ => (hsum' k l).mul_left _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [tsum_mul_left]

section Tiling

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

private theorem tiling_lemma (Γ : Subgroup G) [Countable Γ] (FS : Set G) (hFS : IsFundamentalDomain Γ FS μ)
    (P : Set G) (hP : MeasurableSet P) (f : G → ℝ≥0∞) (hfm : Measurable f) (hfi : ∀ s ∈ Γ, ∀ y, f (s * y) = f y)
    (hcov : ∀ y, f y ≠ 0 → ∃ s ∈ Γ, s * y ∈ P) (huniq : ∀ y ∈ P, ∀ s ∈ Γ, s * y ∈ P → s = 1) :
    ∫⁻ x in FS, f x ∂μ = ∫⁻ x in P, f x ∂μ := by
  open scoped Pointwise in (
    have hmeas : ∀ g : Γ, MeasurableSet (g • P) := fun g => hP.const_smul g
    have hinv : ∀ (g : Γ) (x : G), f (g⁻¹ • x) = f x := fun g x => by
      rw [Subgroup.smul_def, smul_eq_mul]
      exact hfi _ (g⁻¹).2 x
    have hU : MeasurableSet (⋃ g : Γ, g • P) := MeasurableSet.iUnion hmeas
    have hfU : ∀ x, f x = (⋃ g : Γ, g • P).indicator f x := by
      intro x
      by_cases hx : f x = 0
      · simp [Set.indicator_apply, hx]
      · obtain ⟨s, hs, hsP⟩ := hcov x hx
        rw [Set.indicator_of_mem]
        refine Set.mem_iUnion.2 ⟨(⟨s, hs⟩ : Γ)⁻¹, ?_⟩
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact hsP
    have hd : Pairwise (Function.onFun (AEDisjoint μ) fun g : Γ => g • P ∩ FS) := by
      intro g h hgh
      refine Disjoint.aedisjoint ?_
      rw [Set.disjoint_left]
      rintro x ⟨hxg, -⟩ ⟨hxh, -⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hxg hxh
      apply hgh
      have e : ((h⁻¹ * g : Γ) : G) * (g⁻¹ • x) = h⁻¹ • x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.smul_def, smul_eq_mul]
        group
      have h1 := huniq _ hxg _ (h⁻¹ * g).2 (by rw [e]; exact hxh)
      exact (inv_mul_eq_one.mp (Subtype.ext h1)).symm
    rw [hFS.setLIntegral_eq_tsum' f P]
    simp_rw [hinv]
    calc ∫⁻ x in FS, f x ∂μ = ∫⁻ x in FS, (⋃ g : Γ, g • P).indicator f x ∂μ :=
          lintegral_congr fun x => hfU x
      _ = ∫⁻ x in (⋃ g : Γ, g • P) ∩ FS, f x ∂μ := by
          rw [lintegral_indicator hU, Measure.restrict_restrict hU]
      _ = ∫⁻ x in ⋃ g : Γ, g • P ∩ FS, f x ∂μ := by rw [Set.iUnion_inter]
      _ = ∑' g : Γ, ∫⁻ x in g • P ∩ FS, f x ∂μ :=
          lintegral_iUnion₀ (fun g => (hmeas g).nullMeasurableSet.inter hFS.nullMeasurableSet) hd f)

theorem fd_tiling (Γ : Subgroup G) [Countable Γ] (FS : Set G) (hFS : IsFundamentalDomain Γ FS μ)
    (P : Set G) (hP : MeasurableSet P) (f : G → ℂ) (hfm : Measurable f) (hfi : ∀ s ∈ Γ, ∀ y, f (s * y) = f y)
    (hcov : ∀ y, f y ≠ 0 → ∃ s ∈ Γ, s * y ∈ P) (huniq : ∀ y ∈ P, ∀ s ∈ Γ, s * y ∈ P → s = 1)
    (hint : IntegrableOn f FS μ) :
    IntegrableOn f P μ ∧ ∫ x in FS, f x ∂μ = ∫ x in P, f x ∂μ := by
  have key : ∀ g : G → ℝ≥0∞, Measurable g → (∀ s ∈ Γ, ∀ y, g (s * y) = g y) → (∀ y, f y = 0 → g y = 0) →
      ∫⁻ x in FS, g x ∂μ = ∫⁻ x in P, g x ∂μ := fun g hgm hgi hg0 =>
    tiling_lemma μ Γ FS hFS P hP g hgm hgi (fun y hy => hcov y (fun h => hy (hg0 y h))) huniq
  have hP' : IntegrableOn f P μ := by
    have h1 := key (fun x => ‖f x‖ₑ) hfm.enorm (fun s hs y => by simp only [hfi s hs y])
      (fun y hy => by simp [hy])
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in P, ‖f x‖ₑ ∂μ < ⊤
    rw [← h1]
    exact hint.2
  refine ⟨hP', ?_⟩
  have real_eq : ∀ r : G → ℝ, Measurable r → (∀ s ∈ Γ, ∀ y, r (s * y) = r y) → (∀ y, f y = 0 → r y = 0) →
      IntegrableOn r FS μ → IntegrableOn r P μ → ∫ x in FS, r x ∂μ = ∫ x in P, r x ∂μ := by
    intro r hrm hri hr0 h1 h2
    have e1 := key (fun x => ENNReal.ofReal (r x)) hrm.ennreal_ofReal
      (fun s hs y => by simp only [hri s hs y]) (fun y hy => by simp [hr0 y hy])
    have e2 := key (fun x => ENNReal.ofReal (-r x)) hrm.neg.ennreal_ofReal
      (fun s hs y => by simp only [hri s hs y]) (fun y hy => by simp [hr0 y hy])
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2, e1, e2]
  have hre := real_eq (fun x => RCLike.re (f x)) (RCLike.continuous_re.measurable.comp hfm)
    (fun s hs y => by simp only [hfi s hs y]) (fun y hy => by simp [hy]) hint.re hP'.re
  have him := real_eq (fun x => RCLike.im (f x)) (RCLike.continuous_im.measurable.comp hfm)
    (fun s hs y => by simp only [hfi s hs y]) (fun y hy => by simp [hy]) hint.im hP'.im
  rw [integral_re hint, integral_re hP'] at hre
  rw [integral_im hint, integral_im hP'] at him
  exact RCLike.ext hre him

end Tiling

section SlabProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂)

def SlabCover (Ωs : cs.Cl → Set X.B.I.Ginf) : Prop :=
  (∀ y : X.B.I.GA, (∃ n h k, IsDec X u y.2 n h k) → ∃ s ∈ Srat X u, ∃ ρ, s * y ∈ slab cs ρ (Ωs ρ)) ∧
    ∀ (ρ ρ' : cs.Cl) (y : X.B.I.GA) (s : X.B.I.GA), s ∈ Srat X u →
      y ∈ slab cs ρ (Ωs ρ) → s * y ∈ slab cs ρ' (Ωs ρ') → s = 1 ∧ ρ = ρ'

end SlabProps

section SlabClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def SlabCoverC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word)
    (Ωs : (Y.cs u).Cl → Set X.B.I.Ginf),
    X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK →
    (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol (X.Fu u) (Y.cs u) ρ) (Ωs ρ)) →
    SlabCover (Y.cs u) Ωs

def RegroupC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    X.LevelSubgroupNormalized →
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    InHH X u Y.hK → InHH X u' Y.hK →
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    Regroup (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u')

end SlabClosed

section SlabFDPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂)

theorem slabFD_of (hK : X.LevelSubgroupCharacter) (hKL : X.LevelSubgroupNormalized) (hR : FoldReadyX X)
    (hC : ∀ Ωs : cs.Cl → Set X.B.I.Ginf, (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ)) →
      SlabCover cs Ωs) :
    SlabFD F0 cs := by
  intro FS hFS Ωs hΩ f hfm hfi hfsupp hint
  obtain ⟨hcov, huniq⟩ := hC Ωs hΩ
  have : SecondCountableTopology X.B.I.GA := hR.2.1
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  have : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := Formalism.L2.SG.Pf.countable_of_discrete _
  have : Countable (Srat X u) := countable_of_le (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) inf_le_left
  have := @muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar
  have hKm := level_subgroup_measurable X hK hKL
  have hsm : ∀ ρ, MeasurableSet (slab cs ρ (Ωs ρ)) := fun ρ =>
    (hΩ ρ).1.prod ((MeasurableEquiv.mulLeft ((cs.h ρ : X.B.I.Gf) * X.xu u)).measurableSet_image.2 hKm)
  set P := ⋃ ρ, slab cs ρ (Ωs ρ) with hPdef
  have hPm : MeasurableSet P := MeasurableSet.iUnion hsm
  obtain ⟨hIP, hEq⟩ := fd_tiling (X.B.I.muA X.B.μf) (Srat X u) FS hFS P hPm f hfm hfi
    (fun y hy => by
      obtain ⟨s, hs, ρ, hsy⟩ := hcov y (hfsupp y hy)
      exact ⟨s, hs, Set.mem_iUnion.2 ⟨ρ, hsy⟩⟩)
    (fun y hy s hs hsy => by
      obtain ⟨ρ, hρ⟩ := Set.mem_iUnion.1 hy
      obtain ⟨ρ', hρ'⟩ := Set.mem_iUnion.1 hsy
      exact (huniq ρ ρ' y s hs hρ hρ').1)
    hint
  have hIS : ∀ ρ, IntegrableOn f (slab cs ρ (Ωs ρ)) (X.B.I.muA X.B.μf) :=
    fun ρ => hIP.mono_set (Set.subset_iUnion (fun ρ => slab cs ρ (Ωs ρ)) ρ)
  refine ⟨hIS, ?_⟩
  rw [hEq]
  refine integral_iUnion_fintype hsm ?_ hIS
  intro ρ ρ' hne
  refine Set.disjoint_left.2 fun y h1 h2 => hne ?_
  exact (huniq ρ ρ' y 1 (Subgroup.one_mem _) h1 (by simpa using h2)).2

end SlabFDPf

section OOSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (X u u' F0 F0' what₂ rows') in

def OOLintSum : Prop :=
  ∑' t : GTerm X u u' F0 F0' what₂ rows',
    ∫⁻ x in FundOf t, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.pt.1⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

theorem ooLint_of (h : OOLintSum X u u' F0 F0' what₂ rows') : OOLint F0 F0' what₂ rows' (X := X) (u := u) (u' := u') := by
  unfold OOLintSum at h
  unfold OOLint
  intro t
  exact lt_of_le_of_lt (ENNReal.le_tsum t) h

theorem norm_OOt_le (t : GTerm X u u' F0 F0' what₂ rows') :
    ‖OOt t‖ ≤ (∫⁻ x in FundOf t, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.pt.1⁻¹ * x)‖ₑ
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)).toReal := by
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  unfold OOt OO
  refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  rw [norm_rankOneInnerOperator, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

theorem ooAbs_of (h : OOLintSum X u u' F0 F0' what₂ rows') : OOAbs F0 F0' what₂ rows' (X := X) (u := u) (u' := u') := by
  unfold OOLintSum at h
  unfold OOAbs
  exact Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => norm_OOt_le t) (ENNReal.summable_toReal h.ne)

end OOSum

section DT

theorem exists_doubleTransversal {G : Type*} [Group G] (Γ S S' : Subgroup G) (hS : S ≤ Γ) (hS' : S' ≤ Γ) :
    ∃ R : Set G, IsDoubleTransversal Γ S S' R := by
  classical
  let r : Setoid Γ :=
    { r := fun a b => ∃ s ∈ S, ∃ s' ∈ S', s * (a : G) * s' = b
      iseqv := ⟨fun a => ⟨1, S.one_mem, 1, S'.one_mem, by simp⟩,
        fun ⟨s, hs, s', hs', h⟩ => ⟨s⁻¹, S.inv_mem hs, s'⁻¹, S'.inv_mem hs', by rw [← h]; group⟩,
        fun ⟨s, hs, s', hs', h⟩ ⟨t, ht, t', ht', h'⟩ =>
          ⟨t * s, S.mul_mem ht hs, s' * t', S'.mul_mem hs' ht', by rw [← h', ← h]; group⟩⟩ }
  refine ⟨Set.range (fun q : Quotient r => ((Quotient.out q : Γ) : G)), ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact (Quotient.out q).2
  · intro γ hγ
    obtain ⟨s, hs, s', hs', hss⟩ := Quotient.mk_out (s := r) (⟨γ, hγ⟩ : Γ)
    refine ⟨⟨_, ⟨Quotient.mk r ⟨γ, hγ⟩, rfl⟩⟩, ⟨s, hs, s', hs', hss⟩, ?_⟩
    rintro ⟨_, q, rfl⟩ ⟨t, ht, t', ht', htt⟩
    have hq : q = Quotient.mk r ⟨γ, hγ⟩ :=
      (Quotient.out_eq q).symm.trans (Quotient.sound ⟨t, ht, t', ht', htt⟩)
    subst hq
    rfl

end DT

end Formalism.L2.SG.Pf.Slab

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OOLintSumC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOLintSum X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

theorem ooIntAllC_holds_of (h : OOLintSumC) : OOIntAllC := by
  unfold OOLintSumC at h
  exact ooIntAllC_of (fun D X Y u u' h1 h2 h3 => ooLint_of (h D X Y u u' h1 h2 h3))

theorem absConvC_holds_of (h : OOLintSumC) : AbsConvC := by
  unfold OOLintSumC at h
  exact absConvC_of (fun D X Y u u' h1 h2 h3 _ => ooAbs_of (h D X Y u u' h1 h2 h3))

theorem Slab.exists_NOcol_fund {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (ρ : (Y.cs u).Cl) : ∃ Ω, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol (X.Fu u) (Y.cs u) ρ) Ω := by
  have hL := ((Y.rowsOK u).1 _ ((Y.cs u).lam_mem ρ)).1.1
  have := ROsub_discrete X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) hL 1
  obtain ⟨Ω, hΩ⟩ := isSFund_of_discrete X.B.I (ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1)
  refine ⟨Ω, ?_⟩
  have e : ((ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 : Subgroup X.B.I.Ginf) :
      Set X.B.I.Ginf) = NOcol (X.Fu u) (Y.cs u) ρ := by
    ext y
    show y ∈ ROset X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 ↔ _
    constructor
    · rintro ⟨x, n, h1, h2, h3, -⟩
      exact ⟨x, n, h1, h2, h3⟩
    · rintro ⟨x, n, h1, h2, h3⟩
      exact ⟨x, n, h1, h2, h3, by simpa using h3⟩
  rwa [e] at hΩ

theorem kExpansionC_holds_of (hSC : SlabCoverC) (hRG : RegroupC)
    (hNeat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK)
    (hFB : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), FundBridge X)
    (hPM : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), PserMeas X u hK) :
    KExpansionC := by
  intro D X Y u u' hOK hOK' hin hin' hFE hOI hOF hAW hA
  have : SigmaFinite (Formalism.L2.SG.ProjRows.muInf X.B.I) := inferInstance
  have hKL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hR : FoldReadyX X := foldReadyX_holds X
  have : SecondCountableTopology X.B.I.GA := hR.2.1
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hdisc : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  obtain ⟨R, hRt⟩ := exists_doubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u')
    inf_le_left inf_le_left
  have hsd : ∀ r : X.B.I.GA, DiscreteTopology (stab (Srat X u) (Srat X u') r) := fun r =>
    DiscreteTopology.of_subset hdisc (fun y hy => (inf_le_left : Srat X u ≤ _) ((mem_stab _ _ _ _).1 hy).1)
  have hFex : ∀ r : X.B.I.GA, ∃ F : Set X.B.I.GA,
      IsFundamentalDomain (stab (Srat X u) (Srat X u') r) F (X.B.I.muA X.B.μf) := fun r => by
    have := hsd r
    obtain ⟨F, -, hF⟩ := exists_isFund (stab (Srat X u) (Srat X u') r)
    exact ⟨F, hF _⟩
  choose Fs hFs using hFex
  obtain ⟨FS, -, hFS⟩ := exists_fund_srat_holds X u
  choose Ωs hΩs using exists_NOcol_fund Y u
  have hWD : PhWellDef X u Y.hK := phWellDef_holds X u
  have hWD' : PhWellDef X u' Y.hK := phWellDef_holds X u'
  exact kExpansion_of_steps Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK hKL hR (hFB D X) hOK hOK' hin hin'
    (Y.Dt u) (Y.Dt u') (Y.reps u) (Y.reps u') R hRt Fs (fun r _ => hFs r) FS (hFS _) Ωs hΩs hWD hWD'
    (hPM D X u' Y.hK) hA double_coset_single_unfolding
    (slabFD_of (F0 := X.Fu u) (Y.cs u) Y.hK hKL hR (fun Ωs' hΩ' => hSC D X Y u Ωs' hKL (hNeat D X Y u) hΩ'))
    (hRG D X Y u u' hKL hOK hOK' hin hin' hFE hOI hOF hAW hA)

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Slab

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section TilingE

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem fd_tilingE (Γ : Subgroup G) [Countable Γ] (FS : Set G) (hFS : IsFundamentalDomain Γ FS μ)
    (P : Set G) (hP : MeasurableSet P) (f : G → ℝ≥0∞) (hfm : Measurable f) (hfi : ∀ s ∈ Γ, ∀ y, f (s * y) = f y)
    (hcov : ∀ y, f y ≠ 0 → ∃ s ∈ Γ, s * y ∈ P) (huniq : ∀ y ∈ P, ∀ s ∈ Γ, s * y ∈ P → s = 1) :
    ∫⁻ x in FS, f x ∂μ = ∫⁻ x in P, f x ∂μ :=
  tiling_lemma μ Γ FS hFS P hP f hfm hfi hcov huniq

end TilingE

section SlabE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂)

theorem setLIntegral_slab (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant]
    [SigmaFinite (Formalism.L2.SG.ProjRows.muInf I)]
    (K : Set I.Gf) (hK : MeasurableSet K) (Ω : Set I.Ginf) (a : I.Gf) (f : I.GA → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ y : I.Ginf, ∀ k ∈ K, f (y, a * k) = f (y, a)) :
    ∫⁻ x in Ω ×ˢ ((a * ·) '' K), f x ∂(I.muA μf) =
      μf K * ∫⁻ y in Ω, f (y, a) ∂(Formalism.L2.SG.ProjRows.muInf I) := by
  have hA : MeasurableSet ((a * ·) '' K) := (MeasurableEquiv.mulLeft a).measurableSet_image.2 hK
  have hvol : μf ((a * ·) '' K) = μf K := by
    rw [show ((a * ·) '' K) = (fun h => a⁻¹ * h) ⁻¹' K by
      ext z; simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩; simpa using hk
      · intro hz; exact ⟨a⁻¹ * z, hz, by group⟩]
    exact measure_preimage_mul μf a⁻¹ K
  have hin : ∀ y, ∫⁻ z in (a * ·) '' K, f (y, z) ∂μf = f (y, a) * μf K := by
    intro y
    rw [setLIntegral_congr_fun hA (g := fun _ => f (y, a)) ?_, setLIntegral_const, hvol]
    rintro z ⟨k, hk, rfl⟩
    exact hf y k hk
  unfold Formalism.MainNotions.S.AutInst.muA
  rw [← Measure.prod_restrict, lintegral_prod _ hfm.aemeasurable]
  simp_rw [hin]
  have hm : Measurable fun y : I.Ginf => f (y, a) := hfm.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const _ hm, mul_comm]

end SlabE

end Formalism.L2.SG.Pf.Slab

namespace Formalism.L2.SG.Pf.Slab

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section TermsLE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def TermsLE {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)
    (rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA)
    (Ωs : cs.Cl → Set X.B.I.Ginf) : Prop :=
  ∃ (n n' : ℕ) (T : Fin n → Cu X u hK) (T' : Fin n' → Cu X u' hK) (C : ℝ≥0∞), C ≠ ⊤ ∧
    ∀ Λ ∈ what₂,
      ∑' t : {t : GTerm X u u' F0 F0' what₂ rows' // t.lam = Λ},
          ∫⁻ x in FundOf t.1, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.1.pt.1⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ≤
        C * ∑ i, ∑ j, ∫⁻ y in Ωs (cs.base Λ),
          ‖Ph X u hK (T i) (y, (cs.h (cs.base Λ) : X.B.I.Gf) * X.xu u)‖ₑ *
            ∑' δ : Dt', ‖Ph X u' hK (T' j) ((δ : X.B.I.GA) * (y, (cs.h (cs.base Λ) : X.B.I.Gf) * X.xu u))‖ₑ
          ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)

def TermsLEC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (Ωs : (Y.cs u).Cl → Set X.B.I.Ginf),
    (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol (X.Fu u) (Y.cs u) ρ) (Ωs ρ)) →
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    TermsLE X u u' (X.Fu u) (X.Fu u') (Y.cs u) (Y.what₂ u') Y.hK (Y.Dt u') Ωs

theorem enorm_ph_right {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word} (hK : X.LevelSubgroupCharacter)
    (hWD : PhWellDef X u hK) (T : Cu X u hK) (y : X.B.I.GA) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ‖Ph X u hK T (y * (1, κ))‖ₑ = ‖Ph X u hK T y‖ₑ := by
  rw [ph_right_K X u hK hWD T y κ hκ, enorm_mul,
    show ‖X.chi2 κ‖ₑ = 1 by rw [← ofReal_norm, hK.2.2.2.2 κ hκ, ENNReal.ofReal_one], one_mul]

end TermsLE

end Formalism.L2.SG.Pf.Slab

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem Slab.ooLintSum_of {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (hOK : Formalism.L2.SG.WuDecay.FoldOK X u Y.hK) (hOK' : Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK)
    (hNeat : NeatKu X u Y.hK) (hSC : SlabCoverC) (hTL : TermsLEC) :
    OOLintSum X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := by
  have : SigmaFinite (Formalism.L2.SG.ProjRows.muInf X.B.I) := inferInstance
  have hKL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hR : FoldReadyX X := foldReadyX_holds X
  have : SecondCountableTopology X.B.I.GA := hR.2.1
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hdisc : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hR.2.2.2.2
  have : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := Formalism.L2.SG.Pf.countable_of_discrete _
  have : Countable (Srat X u) := countable_of_le _ (Srat X u) inf_le_left
  have hHaar := @muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar
  have : SigmaFinite X.B.μf := X.B.sf
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have : SigmaFinite (X.B.I.muA X.B.μf) := by unfold Formalism.MainNotions.S.AutInst.muA; infer_instance
  have hKm := level_subgroup_measurable X Y.hK hKL
  have hWD : PhWellDef X u Y.hK := phWellDef_holds X u
  have hWD' : PhWellDef X u' Y.hK := phWellDef_holds X u'
  obtain ⟨R, hRt⟩ := exists_doubleTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u')
    inf_le_left inf_le_left
  have hsd : ∀ r : X.B.I.GA, DiscreteTopology (stab (Srat X u) (Srat X u') r) := fun r =>
    DiscreteTopology.of_subset hdisc (fun y hy => (inf_le_left : Srat X u ≤ _) ((mem_stab _ _ _ _).1 hy).1)
  have hFex : ∀ r : X.B.I.GA, ∃ F : Set X.B.I.GA,
      IsFundamentalDomain (stab (Srat X u) (Srat X u') r) F (X.B.I.muA X.B.μf) := fun r => by
    have := hsd r
    obtain ⟨F, -, hF⟩ := exists_isFund (stab (Srat X u) (Srat X u') r)
    exact ⟨F, hF _⟩
  choose Fs hFs using hFex
  obtain ⟨FS, -, hFS⟩ := exists_fund_srat_holds X u
  obtain ⟨FΓ, -, hFΓ⟩ := exists_isFund (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)
  obtain ⟨Dt0, hDt0⟩ := Formalism.L2.SG.Pf.exists_rightTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) inf_le_left
  choose Ωs hΩs using exists_NOcol_fund Y u
  obtain ⟨hcov, huniq⟩ := hSC D X Y u Ωs hKL hNeat hΩs
  obtain ⟨n, n', T, T', C, hC, hle⟩ := hTL D X Y u u' Ωs hΩs hOK hOK'
  obtain ⟨⟨F, hF⟩, Ω₀, a0, hc0, h10, hT⟩ := hOK
  obtain ⟨⟨F', hF'⟩, Ω₀', a0', hc0', h10', hT'⟩ := hOK'
  have hΩc : IsCompact (Ω₀ ∪ Ω₀') := hc0.union hc0'
  have hc := @fold_l2_bound_c X.B.I.GA _ _ _ hR.1 hR.2.1 hR.2.2.1 _ hR.2.2.2.1 (X.B.I.muA X.B.μf) hHaar
  have hDc : Countable (Y.Dt u') := countable_of_sub _ (Y.Dt u') (Y.reps u').1
  have hsm : ∀ ρ, MeasurableSet (slab (Y.cs u) ρ (Ωs ρ)) := fun ρ =>
    (hΩs ρ).1.prod ((MeasurableEquiv.mulLeft (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)).measurableSet_image.2 hKm)
  have hdisj : Pairwise (Function.onFun Disjoint fun ρ => slab (Y.cs u) ρ (Ωs ρ)) := by
    intro ρ ρ' hne
    refine Set.disjoint_left.2 fun y h1 h2 => hne ?_
    exact (huniq ρ ρ' y 1 (Subgroup.one_mem _) h1 (by simpa using h2)).2
  have hPm : MeasurableSet (⋃ ρ, slab (Y.cs u) ρ (Ωs ρ)) := MeasurableSet.iUnion hsm

  have hfin : ∀ i j, ∑ ρ, ∫⁻ y in Ωs ρ, ‖Ph X u Y.hK (T i) (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)‖ₑ *
      ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u))‖ₑ
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    intro i j
    set G : X.B.I.GA → ℝ≥0∞ := fun z =>
      ‖Ph X u Y.hK (T i) z‖ₑ * ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * z)‖ₑ with hG
    have hFD := (hT (T i)).1 _ hΩc Set.subset_union_left
    have hFD' := (hT' (T' j)).1 _ hΩc Set.subset_union_right
    have hU := hc (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u') hdisc inf_le_left inf_le_left
      (Ω₀ ∪ Ω₀') hΩc (Or.inl h10) a0 a0' (Ph X u Y.hK (T i)) (Ph X u' Y.hK (T' j)) hFD hFD' F F' hF hF'
      ((hT (T i)).2 _ hΩc F hF) ((hT' (T' j)).2 _ hΩc F' hF') Dt0 (Y.Dt u') hDt0 (Y.reps u') R hRt Fs
      (fun r _ => hFs r) FΓ (hFΓ _)
    have hPhm : Measurable (Ph X u Y.hK (T i)) := hFD.1
    have hPhm' : Measurable (Ph X u' Y.hK (T' j)) := hFD'.1
    have hinv : ∀ s ∈ Srat X u, ∀ y, Ph X u Y.hK (T i) (s * y) = Ph X u Y.hK (T i) y := hFD.2.1
    have hinv' : ∀ s ∈ Srat X u', ∀ y, Ph X u' Y.hK (T' j) (s * y) = Ph X u' Y.hK (T' j) y := hFD'.2.1
    have hGm : Measurable G :=
      hPhm.enorm.mul (Measurable.ennreal_tsum fun δ => (hPhm'.comp (measurable_const_mul _)).enorm)
    have hGi : ∀ s ∈ Srat X u, ∀ y, G (s * y) = G y := by
      intro s hs y
      simp only [hG]
      rw [hinv s hs y]
      congr 1
      have e := PI.FoldDCUnfold.W.translation_independent X.B.I.GA (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u')
        (Y.Dt u') (Y.Dt u') (Y.reps u') (Y.reps u') s ((inf_le_left : Srat X u ≤ _) hs)
        (fun w => ‖Ph X u' Y.hK (T' j) (w * y)‖ₑ) (fun s' hs' w => by
          show ‖Ph X u' Y.hK (T' j) (s' * w * y)‖ₑ = ‖Ph X u' Y.hK (T' j) (w * y)‖ₑ
          rw [mul_assoc, hinv' s' hs'])
      refine Eq.trans (tsum_congr fun δ => ?_) e
      show ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (s * y))‖ₑ = ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * s * y)‖ₑ
      rw [mul_assoc]
    have hGs : ∀ y, G y ≠ 0 → ∃ s ∈ Srat X u, s * y ∈ ⋃ ρ, slab (Y.cs u) ρ (Ωs ρ) := by
      intro y hy
      have hy1 : Ph X u Y.hK (T i) y ≠ 0 := by
        intro h0; apply hy; simp only [hG, h0, enorm_zero, zero_mul]
      have hd : ∃ n h k, IsDec X u y.2 n h k := by
        by_contra hn; apply hy1; unfold Ph; rw [dif_neg hn]
      obtain ⟨s, hs, ρ, hsy⟩ := hcov y hd
      exact ⟨s, hs, Set.mem_iUnion.2 ⟨ρ, hsy⟩⟩
    have hGu : ∀ y ∈ ⋃ ρ, slab (Y.cs u) ρ (Ωs ρ), ∀ s ∈ Srat X u, s * y ∈ ⋃ ρ, slab (Y.cs u) ρ (Ωs ρ) → s = 1 := by
      intro y hy s hs hsy
      obtain ⟨ρ, hρ⟩ := Set.mem_iUnion.1 hy
      obtain ⟨ρ', hρ'⟩ := Set.mem_iUnion.1 hsy
      exact (huniq ρ ρ' y s hs hρ hρ').1
    have hGK : ∀ ρ, ∀ y : X.B.I.Ginf, ∀ k ∈ X.K2,
        G (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k) = G (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) := by
      intro ρ y k hk
      have hyk : ((y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k) : X.B.I.GA) =
          (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) * (1, k) := by simp
      simp only [hG]
      rw [hyk, enorm_ph_right Y.hK hWD (T i) _ k hk]
      congr 1
      refine tsum_congr fun δ => ?_
      rw [← mul_assoc, enorm_ph_right Y.hK hWD' (T' j) _ k hk]
    have e1 := fd_tilingE (X.B.I.muA X.B.μf) (Srat X u) FS (hFS _) _ hPm G hGm hGi hGs hGu
    have e2 : ∫⁻ z in ⋃ ρ, slab (Y.cs u) ρ (Ωs ρ), G z ∂(X.B.I.muA X.B.μf) =
        ∑ ρ, ∫⁻ z in slab (Y.cs u) ρ (Ωs ρ), G z ∂(X.B.I.muA X.B.μf) := by
      rw [lintegral_iUnion hsm hdisj, tsum_fintype]
    have e3 : ∀ ρ, ∫⁻ z in slab (Y.cs u) ρ (Ωs ρ), G z ∂(X.B.I.muA X.B.μf) =
        X.B.μf X.K2 * ∫⁻ y in Ωs ρ, G (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) :=
      fun ρ => setLIntegral_slab X.B.I X.B.μf X.K2 hKm (Ωs ρ) _ G hGm (hGK ρ)
    have e4 := dcSingleE (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) (Srat X u')
      inf_le_left inf_le_left (Y.Dt u') (Y.reps u') R hRt Fs (fun r _ => hFs r) FS (hFS _)
      (fun z => ‖Ph X u Y.hK (T i) z‖ₑ) (fun z => ‖Ph X u' Y.hK (T' j) z‖ₑ) hPhm.enorm hPhm'.enorm
      (fun s hs y => by simp only [hinv s hs y]) (fun s hs y => by simp only [hinv' s hs y])
    have hK0 : X.B.μf X.K2 ≠ 0 := hKL.2.2.1.ne'
    have hsum : X.B.μf X.K2 * ∑ ρ, ∫⁻ y in Ωs ρ, G (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
      rw [Finset.mul_sum, ← Finset.sum_congr rfl (fun ρ _ => e3 ρ), ← e2, ← e1]
      exact lt_of_eq_of_lt e4 hU.2.1
    rcases ENNReal.mul_lt_top_iff.1 hsum with h | h | h
    · exact h.2
    · exact (hK0 h).elim
    · rw [h]; exact ENNReal.zero_lt_top

  unfold OOLintSum
  set J : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') → ℝ≥0∞ := fun t =>
    ∫⁻ x in FundOf t, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.pt.1⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) with hJ
  set H : Fin n → Fin n' → (Y.cs u).Cl → ℝ≥0∞ := fun i j ρ =>
    ∫⁻ y in Ωs ρ, ‖Ph X u Y.hK (T i) (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)‖ₑ *
      ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (y, ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u))‖ₑ
        ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) with hH
  have h1 : ∑' t, J t = ∑ Λ ∈ Y.what₂ u, ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
      t.lam = Λ}, J t.1 := by
    have e : ∀ t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
        J t = ∑ Λ ∈ Y.what₂ u, if t.lam = Λ then J t else 0 := by
      intro t
      rw [Finset.sum_eq_single_of_mem t.lam t.mem (fun b _ hb => if_neg (fun h => hb h.symm)), if_pos rfl]
    rw [tsum_congr e, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_congr rfl fun Λ _ => ?_
    have hs := tsum_subtype {t | t.lam = Λ} J
    refine Eq.trans ?_ hs.symm
    exact tsum_congr fun b => by simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hinj : Set.InjOn (Y.cs u).base (Y.what₂ u : Set (Submodule (𝓞 D.host.E) (VS D).V)) := by
    intro Λ hΛ Λ' hΛ' h
    rw [← (Y.cs u).base_lam Λ hΛ, ← (Y.cs u).base_lam Λ' hΛ', h]
  have h3 : ∀ i j, ∑ Λ ∈ Y.what₂ u, H i j ((Y.cs u).base Λ) ≤ ∑ ρ, H i j ρ := by
    intro i j
    rw [← Finset.sum_image (f := H i j) (fun Λ hΛ Λ' hΛ' h => hinj hΛ hΛ' h)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [h1]
  calc ∑ Λ ∈ Y.what₂ u, ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, J t.1
      ≤ ∑ Λ ∈ Y.what₂ u, C * ∑ i, ∑ j, H i j ((Y.cs u).base Λ) := Finset.sum_le_sum fun Λ hΛ => hle Λ hΛ
    _ = C * ∑ i, ∑ j, ∑ Λ ∈ Y.what₂ u, H i j ((Y.cs u).base Λ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ C * ∑ i, ∑ j, ∑ ρ, H i j ρ := by
      gcongr with i _ j _
      exact h3 i j
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) ?_
      refine lt_top_iff_ne_top.2 (ENNReal.sum_ne_top.2 fun i _ => ENNReal.sum_ne_top.2 fun j _ => ?_)
      exact (hfin i j).ne

theorem ooLintSumC_of (hSC : SlabCoverC) (hTL : TermsLEC)
    (hNeat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK) :
    OOLintSumC := by
  unfold OOLintSumC
  exact fun D X Y u u' hOK hOK' _ => Slab.ooLintSum_of Y u u' hOK hOK' (hNeat D X Y u) hSC hTL

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.Slab

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section Split

theorem tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (f : ι → α → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) μ) : ∑' i, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑' i, f i x ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← lintegral_finset_sum' s (fun i _ => hf i)]
  exact lintegral_mono fun x => ENNReal.sum_le_tsum s

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def aB {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : X.B.I.Gf :=
  ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u

abbrev NOlam {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Subgroup X.B.I.Ginf :=
  ROsub X (X.Fu u) (X.Fu u) Λ Λ 1

def MajPtC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∃ (n n' : ℕ) (T : Fin n → Cu X u Y.hK) (T' : Fin n' → Cu X u' Y.hK) (c : ℝ≥0∞), c ≠ ⊤ ∧
      ∀ (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (x : X.B.I.Ginf),
        ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.pt.1⁻¹ * x)‖ₑ ≤
          c * ∑ i, ∑ j, ‖Ph X u Y.hK (T i) (x, aB Y u t.lam)‖ₑ *
            ‖Ph X u' Y.hK (T' j) (t.pt⁻¹ * (x, aB Y u t.lam))‖ₑ

def RInvC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (T : Cu X u Y.hK) (T' : Cu X u' Y.hK) (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ r ∈ ROinf t, ∀ x : X.B.I.Ginf,
      ‖Ph X u Y.hK T (r * x, aB Y u t.lam)‖ₑ * ‖Ph X u' Y.hK T' (t.pt⁻¹ * (r * x, aB Y u t.lam))‖ₑ =
        ‖Ph X u Y.hK T (x, aB Y u t.lam)‖ₑ * ‖Ph X u' Y.hK T' (t.pt⁻¹ * (x, aB Y u t.lam))‖ₑ

def CountC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ (T : Cu X u Y.hK) (T' : Cu X u' Y.hK) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u →
      ∀ (E : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') → Set X.B.I.Ginf),
        (∀ t, t.lam = Λ → IsRightTransversal (NOlam X u Λ) (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (E t)) →
        ∀ x : X.B.I.Ginf,
          ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ}, ∑' m : E t.1,
              ‖Ph X u Y.hK T ((m : X.B.I.Ginf) * x, aB Y u Λ)‖ₑ *
                ‖Ph X u' Y.hK T' (t.1.pt⁻¹ * ((m : X.B.I.Ginf) * x, aB Y u Λ))‖ₑ ≤
            M * (‖Ph X u Y.hK T (x, aB Y u Λ)‖ₑ *
              ∑' δ : Y.Dt u', ‖Ph X u' Y.hK T' ((δ : X.B.I.GA) * (x, aB Y u Λ))‖ₑ)

end Split

end Formalism.L2.SG.Pf.Slab

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem Slab.isSFund_fundOf {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) (FundOf t) := by
  have h := fundExistsC_holds D X Y u u' t
  unfold FundOf
  rw [dif_pos h]
  exact h.choose_spec

theorem termsLEC_of (hMaj : MajPtC) (hInv : RInvC) (hCnt : CountC) : TermsLEC := by
  intro D X Y u u' Ωs hΩs hOK hOK'
  have hR : FoldReadyX X := foldReadyX_holds X
  have : SecondCountableTopology X.B.I.GA := hR.2.1
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  obtain ⟨n, n', T, T', c, hc, hM⟩ := hMaj D X Y u u'
  obtain ⟨M, hMt, hcnt⟩ := hCnt D X Y u u'
  obtain ⟨-, Ω₀, a0, hc0, h10, hT⟩ := hOK
  obtain ⟨-, Ω₀', a0', hc0', h10', hT'⟩ := hOK'
  have hPm : ∀ i, Measurable (Ph X u Y.hK (T i)) := fun i => ((hT (T i)).1 Ω₀ hc0 subset_rfl).1
  have hPm' : ∀ j, Measurable (Ph X u' Y.hK (T' j)) := fun j => ((hT' (T' j)).1 Ω₀' hc0' subset_rfl).1
  refine ⟨n, n', T, T', c * M, ENNReal.mul_ne_top hc hMt, fun Λ hΛ => ?_⟩
  set b := (Y.cs u).base Λ with hb
  have hbl : (Y.cs u).lamOf b = Λ := (Y.cs u).base_lam Λ hΛ
  have hL := ((Y.rowsOK u).1 Λ hΛ).1.1
  have := ROsub_discrete X (X.Fu u) (X.Fu u) Λ Λ hL 1
  have : Countable (NOlam X u Λ) := Formalism.L2.SG.Pf.countable_of_discrete _
  have hNset : ((NOlam X u Λ : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = NOcol (X.Fu u) (Y.cs u) b := by
    ext y
    show y ∈ ROset X (X.Fu u) (X.Fu u) Λ Λ 1 ↔ _
    rw [← hbl]
    constructor
    · rintro ⟨x, m, h1, h2, h3, -⟩
      exact ⟨x, m, h1, h2, h3⟩
    · rintro ⟨x, m, h1, h2, h3⟩
      exact ⟨x, m, h1, h2, h3, by simpa using h3⟩
  have hΩ := hΩs b
  rw [← hNset] at hΩ
  have hFdΩ : IsFundamentalDomain (NOlam X u Λ) (Ωs b) (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    isFund_of_strict (NOlam X u Λ) hΩ.1 hΩ.2.1 hΩ.2.2 _
  have hle : ∀ t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), t.lam = Λ →
      ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin ≤ NOlam X u Λ := by
    rintro t ht y ⟨x, m, h1, h2, h3, -⟩
    refine ⟨x, m, h1, h2, by rw [← ht]; exact h3, ?_⟩
    simpa [← ht] using h3
  set E : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') → Set X.B.I.Ginf := fun t =>
    if h : t.lam = Λ then Classical.choose (PI.FoldDCUnfold.W.translation_exists X.B.I.Ginf (NOlam X u Λ)
      (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (hle t h)) else ∅ with hE
  have hEt : ∀ t, t.lam = Λ → IsRightTransversal (NOlam X u Λ)
      (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (E t) := by
    intro t h
    simp only [hE, dif_pos h]
    exact Classical.choose_spec (PI.FoldDCUnfold.W.translation_exists X.B.I.Ginf (NOlam X u Λ)
      (ROsub X (X.Fu u) (X.Fu u') t.lam t.lam' t.lin) (hle t h))
  set a := aB Y u Λ with ha
  set F : Fin n → Fin n' → GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') → X.B.I.Ginf → ℝ≥0∞ :=
    fun i j t x => ‖Ph X u Y.hK (T i) (x, a)‖ₑ * ‖Ph X u' Y.hK (T' j) (t.pt⁻¹ * (x, a))‖ₑ with hF
  have hFm : ∀ i j t, Measurable (F i j t) := fun i j t =>
    ((hPm i).comp (measurable_id.prodMk measurable_const)).enorm.mul
      (((hPm' j).comp ((measurable_const_mul _).comp (measurable_id.prodMk measurable_const))).enorm)

  have hij : ∀ i j, ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
      ∫⁻ x in FundOf t.1, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ≤
        M * ∫⁻ y in Ωs b, ‖Ph X u Y.hK (T i) (y, a)‖ₑ *
          ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (y, a))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    intro i j
    have hU : ∀ t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
        ∫⁻ x in FundOf t.1, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
          ∫⁻ x in Ωs b, ∑' m : E t.1, F i j t.1 ((m : X.B.I.Ginf) * x) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
      intro t
      have hS := isSFund_fundOf Y u u' t.1
      have := ROsub_discrete X (X.Fu u) (X.Fu u') t.1.lam t.1.lam' (by rw [t.2]; exact hL) t.1.lin
      have : Countable (ROsub X (X.Fu u) (X.Fu u') t.1.lam t.1.lam' t.1.lin) :=
        Formalism.L2.SG.Pf.countable_of_discrete _
      have hFd : IsFundamentalDomain (ROsub X (X.Fu u) (X.Fu u') t.1.lam t.1.lam' t.1.lin) (FundOf t.1)
          (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
        isFund_of_strict _ hS.1 hS.2.1 hS.2.2 _
      have hab : aB Y u t.1.lam = a := by rw [t.2]
      refine (lintegralTransversalSum X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) (NOlam X u Λ) _ (hle t.1 t.2)
        (FundOf t.1) hFd (Ωs b) hFdΩ (E t.1) (hEt t.1 t.2) (F i j t.1) (hFm i j t.1) ?_).symm
      intro s hs y
      have h := hInv D X Y u u' (T i) (T' j) t.1 s hs y
      rw [hab] at h
      exact h
    calc ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
          ∫⁻ x in FundOf t.1, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)
        = ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
          ∫⁻ x in Ωs b, ∑' m : E t.1, F i j t.1 ((m : X.B.I.Ginf) * x) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) :=
          tsum_congr hU
      _ ≤ ∫⁻ x in Ωs b, ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
            ∑' m : E t.1, F i j t.1 ((m : X.B.I.Ginf) * x) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
          refine tsum_lintegral_le _ fun t => ?_
          have : Countable (E t.1) := by
            have h := (hEt t.1 t.2).1
            exact Function.Injective.countable (f := fun s : E t.1 => (⟨(s : X.B.I.Ginf), h s.2⟩ : NOlam X u Λ))
              (by intro p q hpq; apply Subtype.ext; have := congrArg Subtype.val hpq; exact this)
          exact (Measurable.ennreal_tsum fun m => (hFm i j t.1).comp (measurable_const_mul _)).aemeasurable
      _ ≤ ∫⁻ x in Ωs b, M * (‖Ph X u Y.hK (T i) (x, a)‖ₑ *
            ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (x, a))‖ₑ) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) :=
          lintegral_mono fun x => hcnt (T i) (T' j) Λ hΛ E hEt x
      _ = _ := lintegral_const_mul' _ _ hMt

  calc ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
        ∫⁻ x in FundOf t.1, ‖X.Wu u x‖ₑ * ‖X.Wu u' (t.1.pt.1⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)
      ≤ ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
        ∫⁻ x in FundOf t.1, c * ∑ i, ∑ j, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
        refine ENNReal.tsum_le_tsum fun t => lintegral_mono fun x => ?_
        have h := hM t.1 x
        have hab : aB Y u t.1.lam = a := by rw [t.2]
        rw [hab] at h
        exact h
    _ = c * ∑ i, ∑ j, ∑' t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
        ∫⁻ x in FundOf t.1, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
        have hint : ∀ t : {t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // t.lam = Λ},
            ∫⁻ x in FundOf t.1, c * ∑ i, ∑ j, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
              c * ∑ i, ∑ j, ∫⁻ x in FundOf t.1, F i j t.1 x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
          intro t
          rw [lintegral_const_mul' _ _ hc, lintegral_finset_sum _ (fun i _ => Finset.measurable_sum _
            (fun j _ => hFm i j t.1))]
          congr 1
          exact Finset.sum_congr rfl fun i _ => lintegral_finset_sum _ (fun j _ => hFm i j t.1)
        rw [tsum_congr hint, ENNReal.tsum_mul_left]
        congr 1
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        exact Finset.sum_congr rfl fun i _ => Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
      _ ≤ c * ∑ i, ∑ j, M * ∫⁻ y in Ωs b, ‖Ph X u Y.hK (T i) (y, a)‖ₑ *
          ∑' δ : Y.Dt u', ‖Ph X u' Y.hK (T' j) ((δ : X.B.I.GA) * (y, a))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
        gcongr with i _ j _
        exact hij i j
      _ = _ := by
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]; rfl

theorem ooLintSumC_of_parts (hSC : SlabCoverC) (hMaj : MajPtC) (hInv : RInvC) (hCnt : CountC)
    (hNeat : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK) :
    OOLintSumC :=
  ooLintSumC_of hSC (termsLEC_of hMaj hInv hCnt) hNeat

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.Pf.Slab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem Slab.mem_srat_of_nlam {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {x : X.B.I.GA} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hx : RatLink X x m) (hm : m ∈ NLam Λ (lf D (X.Fu u))) : x ∈ Srat X u := by
  have h1 := nLamNinf_holds D X u Λ x m hx hm
  have h2 := nLamNfin_holds D X u Λ x m hx hm
  refine Subgroup.mem_inf.2 ⟨ratLink_mem X hx, Subgroup.subset_closure ⟨fun v => (h1 v).1, h2.1, h2.2.1⟩⟩

theorem rInvC_of (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) : RInvC := by
  intro D X Y u u' T T' t r hr x
  obtain ⟨xr, m, hRL, hrx, hm, hm'⟩ := hr
  have hK := Y.hK
  have hxS : xr ∈ Srat X u := mem_srat_of_nlam hRL hm
  have hb : (Y.cs u).lamOf ((Y.cs u).base t.lam) = t.lam := (Y.cs u).base_lam t.lam t.mem
  obtain ⟨hκ, -⟩ := hNC D X Y u ((Y.cs u).base t.lam) xr m (by rw [hb]; exact hm) hRL
  set a := aB Y u t.lam with ha
  have hκ' : (a⁻¹ * xr.2 * a)⁻¹ ∈ X.K2 := hK.2.2.1 _ hκ
  have e1 : ((r * x, a) : X.B.I.GA) = xr * (x, a) * (1, (a⁻¹ * xr.2 * a)⁻¹) := by
    subst hrx
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_mul, Prod.snd_one]
      group
  have hγ : RatLink X t.pt t.lin := t.rep.2.1
  have hy : RatLink X (t.pt⁻¹ * xr * t.pt) (t.lin⁻¹ * m * t.lin) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X hγ) hRL) hγ
  have hyS : t.pt⁻¹ * xr * t.pt ∈ Srat X u' := mem_srat_of_nlam hy hm'
  have e2 : t.pt⁻¹ * ((r * x, a) : X.B.I.GA) =
      (t.pt⁻¹ * xr * t.pt) * (t.pt⁻¹ * (x, a)) * (1, (a⁻¹ * xr.2 * a)⁻¹) := by
    rw [e1]; group
  have hWD : PhWellDef X u Y.hK := phWellDef_holds X u
  have hWD' : PhWellDef X u' Y.hK := phWellDef_holds X u'
  have hL := phLeftInv_of X u Y.hK hWD (ratLevi_holds X u) (psiProd_holds X u)
  have hL' := phLeftInv_of X u' Y.hK hWD' (ratLevi_holds X u') (psiProd_holds X u')
  rw [e2, e1, enorm_ph_right Y.hK hWD T _ _ hκ', enorm_ph_right Y.hK hWD' T' _ _ hκ',
    hL T xr hxS, hL' T' _ hyS]

end Formalism.L2.SG.Pf
