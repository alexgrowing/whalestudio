import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.DivisionPairOfAdelicFormsFaceColumnsData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualIndexFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.ReindexBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace Unfolding

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsHaarMeasure]

theorem measure_inter_eq_of_isFundamentalDomain {s s' : Set G} (hs : IsFundamentalDomain Γ s μ)
    (hs' : IsFundamentalDomain Γ s' μ) {A : Set G} (hA : MeasurableSet A)
    (hinv : ∀ γ ∈ Γ, ∀ g, γ * g ∈ A ↔ g ∈ A) : μ (s ∩ A) = μ (s' ∩ A) := by
  rw [Set.inter_comm, Set.inter_comm s' A]
  refine hs.measure_set_eq hs' hA fun γ => ?_
  ext g
  simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul]
  exact hinv γ γ.2 g

theorem false_of_isFundamentalDomain {s : Set G} (hs : IsFundamentalDomain Γ s μ)
    (U : ℕ → Set G) (hinv : ∀ n, ∀ γ ∈ Γ, ∀ g, γ * g ∈ U n ↔ g ∈ U n)
    (hcov : ∀ g, ∃ n, g ∈ U n) (hnull : ∀ n, μ (s ∩ U n) = 0) : False := by
  have hU : ∀ n, μ (U n) = 0 := by
    intro n
    refine hs.measure_zero_of_invariant (U n) (fun γ => ?_) (by rw [Set.inter_comm]; exact hnull n)
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    exact hinv n _ (Γ.inv_mem γ.2) g
  have huniv : μ Set.univ = 0 := by
    rw [show (Set.univ : Set G) = ⋃ n, U n from (Set.iUnion_eq_univ_iff.2 hcov).symm]
    exact measure_iUnion_null hU
  exact NeZero.ne μ (Measure.measure_univ_eq_zero.1 huniv)

theorem exists_iff_forall_isFundamentalDomain (k : ℕ) (U : ℝ → Set G)
    (hU : ∀ t, MeasurableSet (U t)) (hinv : ∀ t, ∀ γ ∈ Γ, ∀ g, γ * g ∈ U t ↔ g ∈ U t)
    (hcov : ∀ g, ∃ n : ℕ, g ∈ U ((n : ℝ) + 1)) (hex : ∃ s, IsFundamentalDomain Γ s μ) :
    (∃ s, IsFundamentalDomain Γ s μ ∧ ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧
      ∀ t : ℝ, 0 < t → μ (s ∩ U t) = C * ENNReal.ofReal (t ^ k)) ↔
    (∀ s, IsFundamentalDomain Γ s μ → μ (s ∩ U 1) < ⊤ ∧
      ∀ t : ℝ, 0 < t → μ (s ∩ U t) = ENNReal.ofReal t ^ k * μ (s ∩ U 1)) := by
  constructor
  · rintro ⟨s, hs, C, -, hCtop, hC⟩ s' hs'
    have e : ∀ t, μ (s' ∩ U t) = μ (s ∩ U t) := fun t =>
      measure_inter_eq_of_isFundamentalDomain hs' hs (hU t) (hinv t)
    have h1 : μ (s ∩ U 1) = C := by rw [hC 1 one_pos]; simp
    refine ⟨by rw [e, h1]; exact hCtop, fun t ht => ?_⟩
    rw [e, e, h1, hC t ht, ENNReal.ofReal_pow ht.le, mul_comm]
  · intro hB
    obtain ⟨s, hs⟩ := hex
    obtain ⟨hfin, hscale⟩ := hB s hs
    refine ⟨s, hs, μ (s ∩ U 1), pos_iff_ne_zero.2 fun h0 => ?_, hfin, fun t ht => ?_⟩
    · refine false_of_isFundamentalDomain hs (fun n => U ((n : ℝ) + 1)) (fun n => hinv _) hcov
        fun n => ?_
      rw [hscale _ (by positivity), h0, mul_zero]
    · rw [hscale t ht, ENNReal.ofReal_pow ht.le, mul_comm]

end Generic

section First

attribute [local instance] archMulAction

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vecStabGroup_smul_vecAt (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (x₀ : W) {γ : archUnitary h v} (hγ : γ ∈ vecStabGroup h v La x₀) :
    γ • vecAt v x₀ = vecAt v x₀ := by
  obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hγ
  change archEmbed h v (δ : h.unitaryGroup) • vecAt v x₀ = vecAt v x₀
  rw [archEmbed_smul_vecAt]
  exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hδ)

theorem below_invariant (h : HermitianForm F E W) (v : Basis ι E W) (M : Majorant h v)
    (La : AddSubgroup W) (x₀ : W) (t : ℝ) :
    ∀ γ ∈ vecStabGroup h v La x₀, ∀ g : archUnitary h v,
      γ * g ∈ {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t} ↔
        g ∈ {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t} := by
  intro γ hγ g
  simp only [Set.mem_ofPred_eq, invApply_eq_smul, _root_.mul_inv_rev, mul_smul,
    vecStabGroup_smul_vecAt h v La x₀ ((vecStabGroup h v La x₀).inv_mem hγ)]

theorem vecStabGroup_discrete (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W)
    (hLa : IsLattice E La) (x₀ : W) : DiscreteTopology (vecStabGroup h v La x₀) := by
  have := ArchLatticeDiscrete.proof h v La hLa
  have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
  exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)

theorem unfolding_exists_iff_forall (h : HermitianForm F E W) (v : Basis ι E W) (M : Majorant h v)
    (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ) (La : AddSubgroup W) (x₀ : W)
    (hLa : IsDIntegral h D La) :
    (∃ FD : Set (archUnitary h v), IsFundamentalDomain (vecStabGroup h v La x₀) FD μ ∧
      ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1)))) ↔
    (∀ s : Set (archUnitary h v), IsFundamentalDomain (vecStabGroup h v La x₀) s μ →
      μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < 1}) < ⊤ ∧
      ∀ t : ℝ, 0 < t → μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
        ENNReal.ofReal t ^ (2 * finrank ℚ F * (finrank E W - 1)) *
          μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < 1})) := by
  have hdisc := vecStabGroup_discrete h v La hLa.isLattice x₀
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨FD, -, hFD⟩ := DiscreteFundamentalDomain.proof (archUnitary h v) μ _ hdisc
  exact exists_iff_forall_isFundamentalDomain (2 * finrank ℚ F * (finrank E W - 1))
    (fun t => {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t})
    (fun t => measurableSet_below M (vecAt v x₀) t) (below_invariant h v M La x₀)
    (fun g => by
      obtain ⟨n, hn⟩ := exists_nat_gt (M.len (invApply g (vecAt v x₀)))
      exact ⟨n, hn.trans (lt_add_one _)⟩) ⟨FD, hFD⟩

theorem UnfoldingIntegral.iff_forall (h : HermitianForm F E W) (v : Basis ι E W) :
    UnfoldingIntegral.Statement h v ↔
      ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
        (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
        h.toSesq x₀ x₀ = 0 → ∀ s : Set (archUnitary h v),
        IsFundamentalDomain (vecStabGroup h v La x₀) s μ →
        μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < 1}) < ⊤ ∧
        ∀ t : ℝ, 0 < t → μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          ENNReal.ofReal t ^ (2 * finrank ℚ F * (finrank E W - 1)) *
            μ (s ∩ {g | M.len (invApply g (vecAt v x₀)) < 1}) := by
  constructor
  · intro hA M μ _ D La x₀ hLa hx₀ hne hiso
    exact (unfolding_exists_iff_forall h v M μ D La x₀ hLa).1 (hA M μ D La x₀ hLa hx₀ hne hiso)
  · intro hB M μ _ D La x₀ hLa hx₀ hne hiso
    exact (unfolding_exists_iff_forall h v M μ D La x₀ hLa).2 (hB M μ D La x₀ hLa hx₀ hne hiso)

end First

section IndefiniteRowSideFullHecke

attribute [local instance] archMulAction

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {N : ℕ}
variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

theorem realMeas_symm_apply (y : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) :
    (realMeas h v).symm y = (realEquiv h v).symm y :=
  (realMeas h v).injective (by
    rw [MeasurableEquiv.apply_symm_apply, realMeas_apply, MulEquiv.apply_symm_apply])

theorem realHomeo_symm_apply (y : IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) :
    (realHomeo h v).symm y = (realEquiv h v).symm y :=
  (realHomeo h v).injective (by
    rw [Homeomorph.apply_symm_apply, realHomeo_apply, MulEquiv.apply_symm_apply])

theorem continuous_realEquiv : Continuous (realEquiv h v) := by
  have := (realHomeo h v).continuous
  rwa [show ⇑(realHomeo h v) = ⇑(realEquiv h v) from funext (realHomeo_apply h v)] at this

theorem continuous_realEquiv_symm : Continuous (realEquiv h v).symm := by
  have := (realHomeo h v).symm.continuous
  rwa [show ⇑(realHomeo h v).symm = ⇑(realEquiv h v).symm from funext (realHomeo_symm_apply h v)]
    at this

theorem isHaarMeasure_map_realMeas (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] :
    (μ.map (realMeas h v)).IsHaarMeasure := by
  rw [show ⇑(realMeas h v) = ⇑(realEquiv h v) from funext (realMeas_apply h v)]
  exact (realEquiv h v).isHaarMeasure_map μ (continuous_realEquiv h v)
    (continuous_realEquiv_symm h v)

theorem isHaarMeasure_map_realMeas_symm (μ : Measure (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)))
    [μ.IsHaarMeasure] : (μ.map (realMeas h v).symm).IsHaarMeasure := by
  rw [show ⇑(realMeas h v).symm = ⇑(realEquiv h v).symm from funext (realMeas_symm_apply h v)]
  exact (realEquiv h v).symm.isHaarMeasure_map μ (continuous_realEquiv_symm h v)
    (continuous_realEquiv h v)

def vecStabEquiv (L : Submodule (𝓞 E) (Fin N → E)) (x₀ : W) :
    vecStabGroup h v (latOf v L) x₀ ≃*
      IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀) :=
  ((realEquiv h v).subgroupMap _).trans (MulEquiv.subgroupCongr (vecStabGroup.equiv L x₀))

theorem vecStabEquiv_coe (L : Submodule (𝓞 E) (Fin N → E)) (x₀ : W)
    (γ : vecStabGroup h v (latOf v L) x₀) :
    ((vecStabEquiv h v L x₀ γ : IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀)) :
      IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)) = realEquiv h v γ := rfl

theorem realMeas_semiconj (L : Submodule (𝓞 E) (Fin N → E)) (x₀ : W)
    (g : IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀)) (x : archUnitary h v) :
    realMeas h v ((vecStabEquiv h v L x₀).symm g • x) = g • realMeas h v x := by
  rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, realMeas_apply,
    realMeas_apply, map_mul, ← vecStabEquiv_coe, MulEquiv.apply_symm_apply]

theorem lintegral_belowInd (M : Majorant h v) (μ : Measure (archUnitary h v)) (x₀ : W)
    (s : Set (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v))) (t : ℝ) :
    ∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd (majOf M) (v.equivFun x₀) t g
        ∂(μ.map (realMeas h v)) =
      μ (realMeas h v ⁻¹' s ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) := by
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
  have hfun : ∀ g, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd (majOf M) (v.equivFun x₀) t (realMeas h v g) =
      {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t}.indicator 1 g := by
    intro g
    simp only [IndefiniteRowSideFullHecke.FiniteCovolume.belowInd, Set.indicator_apply, Set.mem_ofPred_eq, realMeas_apply,
      Majorant.len.equiv, invApply.equiv, vecAt.equiv, Pi.one_apply]
  have hm : MeasurableSet {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t} :=
    measurableSet_below M (vecAt v x₀) t
  simp_rw [hfun]
  rw [lintegral_indicator_one hm, Measure.restrict_apply hm, Set.inter_comm]

omit h in

theorem exponent_eq (v : Basis (Fin N) E W) :
    2 * finrank ℚ F * (finrank E W - 1) = 2 * IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E * (N - 1) := by
  rw [fDeg.equiv (F := F) (E := E), Module.finrank_eq_card_basis v, Fintype.card_fin]

end IndefiniteRowSideFullHecke

section Directions

attribute [local instance] archMulAction

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {N : ℕ}
variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

theorem unfolding_matrix_of_form (hA : UnfoldingIntegral.Statement h v) :
    ∀ (M : IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v)) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E))
      (v₀ : Fin N → E), IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v) D L → v₀ ∈ L → v₀ ≠ 0 →
      (divisionPairOfAdelicFormsFaceColumnsData h v).h v₀ v₀ = 0 →
      ∀ μ : Measure (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)), μ.IsHaarMeasure →
      ∀ s : Set (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)),
        IsFundamentalDomain (IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L v₀) s μ →
        (∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ 1 g ∂μ) < ⊤ ∧
        ∀ t : ℝ, 0 < t → (∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ t g ∂μ) =
          ENNReal.ofReal t ^ (2 * IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E * (N - 1)) *
            ∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ 1 g ∂μ := by
  rw [UnfoldingIntegral.iff_forall] at hA
  intro M' D L v₀ hL hv₀ hne hiso μ' hμ' s' hs'
  obtain ⟨M, rfl⟩ := (Majorant.equiv (h := h) (v := v)).2 M'
  obtain ⟨x₀, rfl⟩ := v.equivFun.surjective v₀
  have hLa := (IsDIntegral.equiv_of_dualIndexFinite (DualIndexFinite.proof h) D L).2 hL
  have hne' : x₀ ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  have hiso' : h.toSesq x₀ x₀ = 0 := by
    rw [← HermSpace.h.equiv h v]
    exact hiso
  have := isHaarMeasure_map_realMeas_symm h v μ'
  have hμ : (μ'.map (realMeas h v).symm).map (realMeas h v) = μ' :=
    MeasurableEquiv.map_map_symm _
  have hs : IsFundamentalDomain (vecStabGroup h v (latOf v L) x₀) (realMeas h v ⁻¹' s')
      (μ'.map (realMeas h v).symm) := by
    refine hs'.preimage_of_equiv ?_ (vecStabEquiv h v L x₀).symm.bijective
      (fun g x => realMeas_semiconj h v L x₀ g x)
    have := ((realMeas h v).measurable.measurePreserving (μ'.map (realMeas h v).symm))
    rw [hμ] at this
    exact this.quasiMeasurePreserving
  obtain ⟨h1, h2⟩ := hA M (μ'.map (realMeas h v).symm) D (latOf v L) x₀ hLa hv₀ hne' hiso' _ hs
  rw [← hμ]
  simp only [lintegral_belowInd]
  refine ⟨h1, fun t ht => ?_⟩
  rw [h2 t ht, exponent_eq (F := F) v]

theorem unfolding_form_of_matrix
    (hB : ∀ (M : IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v)) (D : ℕ)
      (L : Submodule (𝓞 E) (Fin N → E)) (v₀ : Fin N → E),
      IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v) D L → v₀ ∈ L → v₀ ≠ 0 →
      (divisionPairOfAdelicFormsFaceColumnsData h v).h v₀ v₀ = 0 →
      ∀ μ : Measure (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)), μ.IsHaarMeasure →
      ∀ s : Set (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)),
        IsFundamentalDomain (IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L v₀) s μ →
        (∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ 1 g ∂μ) < ⊤ ∧
        ∀ t : ℝ, 0 < t → (∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ t g ∂μ) =
          ENNReal.ofReal t ^ (2 * IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E * (N - 1)) *
            ∫⁻ g in s, IndefiniteRowSideFullHecke.FiniteCovolume.belowInd M v₀ 1 g ∂μ) :
    UnfoldingIntegral.Statement h v := by
  rw [UnfoldingIntegral.iff_forall]
  intro M μ _ D La x₀ hLa hx₀ hne hiso s hs
  obtain ⟨L, rfl⟩ := exists_latOf (v := v) hLa.isLattice.smul_mem
  have hL := ((IsDIntegral.equiv (h := h) D L).1 hLa).1
  have hne' : v.equivFun x₀ ≠ 0 := fun h0 => hne (v.equivFun.injective (by rw [h0, map_zero]))
  have hiso' : (divisionPairOfAdelicFormsFaceColumnsData h v).h (v.equivFun x₀) (v.equivFun x₀) = 0 := by
    rw [HermSpace.h.equiv]
    exact hiso
  have := isHaarMeasure_map_realMeas h v μ
  have hs' : IsFundamentalDomain (IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀))
      (realMeas h v '' s) (μ.map (realMeas h v)) := by
    refine hs.image_of_equiv (realMeas h v).toEquiv ?_ (vecStabEquiv h v L x₀).symm.toEquiv
      (fun g x => realMeas_semiconj h v L x₀ g x)
    have := ((realMeas h v).symm.measurable.measurePreserving (μ.map (realMeas h v)))
    rw [MeasurableEquiv.map_symm_map] at this
    exact this.quasiMeasurePreserving
  obtain ⟨h1, h2⟩ := hB (majOf M) D L (v.equivFun x₀) hL hx₀ hne' hiso' (μ.map (realMeas h v))
    inferInstance _ hs'
  simp only [lintegral_belowInd, MeasurableEquiv.preimage_image] at h1 h2
  refine ⟨h1, fun t ht => ?_⟩
  rw [h2 t ht, exponent_eq (F := F) v]

end Directions

section Transport

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G']
  [BorelSpace G']

theorem forall_isFundamentalDomain_of_mulEquiv (Φ : G ≃* G') (hΦ : Continuous Φ)
    (hΦ' : Continuous Φ.symm) {Γ : Subgroup G} {Γ' : Subgroup G'} (hΓ : Γ.map Φ.toMonoidHom = Γ')
    (U : ℝ → Set G) (U' : ℝ → Set G') (hU : ∀ t, Φ ⁻¹' U' t = U t) (k : ℕ)
    (hB : ∀ μ' : Measure G', μ'.IsHaarMeasure → ∀ s' : Set G', IsFundamentalDomain Γ' s' μ' →
      μ' (s' ∩ U' 1) < ⊤ ∧ ∀ t : ℝ, 0 < t → μ' (s' ∩ U' t) = ENNReal.ofReal t ^ k * μ' (s' ∩ U' 1))
    (μ : Measure G) [μ.IsHaarMeasure] (s : Set G) (hs : IsFundamentalDomain Γ s μ) :
    μ (s ∩ U 1) < ⊤ ∧ ∀ t : ℝ, 0 < t → μ (s ∩ U t) = ENNReal.ofReal t ^ k * μ (s ∩ U 1) := by
  let Φh : G ≃ₜ G' := ⟨Φ.toEquiv, hΦ, hΦ'⟩
  let Φm : G ≃ᵐ G' := Φh.toMeasurableEquiv
  have hcoe : ⇑Φm = ⇑Φ := rfl
  have hHaar : (μ.map Φm).IsHaarMeasure := by
    rw [hcoe]
    exact Φ.isHaarMeasure_map μ hΦ hΦ'
  let Ψ : Γ ≃* Γ' := (Φ.subgroupMap Γ).trans (MulEquiv.subgroupCongr hΓ)
  have hΨ : ∀ γ : Γ, ((Ψ γ : Γ') : G') = Φ γ := fun _ => rfl
  have hs' : IsFundamentalDomain Γ' (Φm '' s) (μ.map Φm) := by
    refine hs.image_of_equiv Φm.toEquiv ?_ Ψ.symm.toEquiv (fun g x => ?_)
    · have := Φm.symm.measurable.measurePreserving (μ.map Φm)
      rw [MeasurableEquiv.map_symm_map] at this
      exact this.quasiMeasurePreserving
    · change Φ ((Ψ.symm g : G) * x) = (g : G') * Φ x
      rw [map_mul, ← hΨ, MulEquiv.apply_symm_apply]
  have key : ∀ t, (μ.map Φm) (Φm '' s ∩ U' t) = μ (s ∩ U t) := by
    intro t
    rw [MeasurableEquiv.map_apply, Set.preimage_inter, MeasurableEquiv.preimage_image, hcoe, hU]
  obtain ⟨h1, h2⟩ := hB (μ.map Φm) hHaar _ hs'
  simp only [key] at h1 h2
  exact ⟨h1, h2⟩

end Transport

section Reindex

open Reindex

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem archReindex_archReindexBack (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (g : archUnitary h (v.reindex e)) : archReindex h v e (archReindexBack h v e g) = g := by
  apply Subtype.ext
  funext w
  exact reGL_reGL_symm e _

theorem continuous_archReindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    Continuous (archReindex h v e) :=
  Continuous.subtype_mk (continuous_pi fun w =>
    (continuous_reGL e).comp ((continuous_apply w).comp continuous_subtype_val)) _

def archReindexEquiv (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    archUnitary h v ≃* archUnitary h (v.reindex e) where
  toFun := archReindex h v e
  invFun := archReindexBack h v e
  left_inv := archReindexBack_archReindex h v e
  right_inv := archReindex_archReindexBack h v e
  map_mul' := map_mul _

theorem vecStabGroup_reindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (La : AddSubgroup W) (x₀ : W) :
    (vecStabGroup h v La x₀).map (archReindexEquiv h v e).toMonoidHom =
      vecStabGroup h (v.reindex e) La x₀ := by
  unfold vecStabGroup
  rw [Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun γ => archReindex_archEmbed h v e _

theorem UnfoldingIntegral.of_reindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (hS : UnfoldingIntegral.Statement h (v.reindex e)) : UnfoldingIntegral.Statement h v := by
  rw [UnfoldingIntegral.iff_forall] at hS ⊢
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  exact forall_isFundamentalDomain_of_mulEquiv (archReindexEquiv h v e)
    (continuous_archReindex h v e) (continuous_archReindexBack h v e)
    (vecStabGroup_reindex h v e La x₀)
    (fun t => {g : archUnitary h v | M.len (invApply g (vecAt v x₀)) < t})
    (fun t => {g | (majReindex e M).len (invApply g (vecAt (v.reindex e) x₀)) < t})
    (fun t => by
      ext g
      exact iff_of_eq (congrArg (· < t) (len_invApply_reindex e M g x₀)))
    _ (fun μ' hμ' s' hs' => by
      have := hμ'
      exact hS (majReindex e M) μ' D La x₀ hLa hx₀ hne hiso s' hs') μ

end Reindex

universe u w x

theorem unfolding_form_of_matrix_all (hB : IndefiniteRowSideFullHecke.FiniteCovolume.Unfolding.Statement) :
    ∀ (F : Type u) (E : Type) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
      (W : Type w) [AddCommGroup W] [Module E W] (ι : Type x) [Fintype ι] [DecidableEq ι]
      (h : HermitianForm F E W) (v : Basis ι E W), UnfoldingIntegral.Statement h v := by
  intro F E _ _ _ _ _ _ _ _ W _ _ ι _ _ h v
  have := isCMField (F := F) (E := E)
  refine UnfoldingIntegral.of_reindex h v (Fintype.equivFin ι) ?_
  exact Unfolding.unfolding_form_of_matrix h (v.reindex (Fintype.equivFin ι))
    (hB E (Fintype.card ι) (divisionPairOfAdelicFormsFaceColumnsData h (v.reindex (Fintype.equivFin ι))))

theorem unfolding_matrix_of_form_all
    (hA : ∀ (F E : Type) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
      (W : Type) [AddCommGroup W] [Module E W] (ι : Type) [Fintype ι] [DecidableEq ι]
      (h : HermitianForm F E W) (v : Basis ι E W), UnfoldingIntegral.Statement h v) :
    IndefiniteRowSideFullHecke.FiniteCovolume.Unfolding.Statement := by
  intro E _ _ _ N V
  have := Unfolding.unfolding_matrix_of_form (hermitianFormOfMatrix (maximalRealSubfield E) V) (Pi.basisFun E (Fin N))
    (hA _ E _ (Fin N) _ _)
  rwa [matrixHermSpace_surjective] at this

theorem equiv :
    (∀ (F E : Type) [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
      (W : Type) [AddCommGroup W] [Module E W] (ι : Type) [Fintype ι] [DecidableEq ι]
      (h : HermitianForm F E W) (v : Basis ι E W), UnfoldingIntegral.Statement h v) ↔
    IndefiniteRowSideFullHecke.FiniteCovolume.Unfolding.Statement :=
  ⟨Unfolding.unfolding_matrix_of_form_all, fun hB => Unfolding.unfolding_form_of_matrix_all.{0, 0, 0} hB⟩

end Unfolding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
