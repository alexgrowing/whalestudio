import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.WeightedUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MeasureInterEqOfIsFundamentalDomain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder

universe u

section First

open GroundTheory.Heights₂.Heights.FiniteCovolume

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def wlen {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) (c : InfinitePlace E → ℝ)
    (y : InfinitePlace E → ι → ℂ) : ℝ :=
  Real.sqrt (∑ w, c w * (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem wlen_invApply_of_mem_stab {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (c : InfinitePlace E → ℝ) {k : archUnitary h v} (hk : k ∈ M.stab) (y : InfinitePlace E → ι → ℂ) :
    wlen M c (invApply k y) = wlen M c y := by
  unfold wlen
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have hk' := inv_mem hk
  rw [Majorant.stab, Subgroup.mem_subgroupOf] at hk'
  have hA := mem_unitaryGroupMatrix.1 ((Subgroup.mem_pi _).1 hk' w (Set.mem_univ w))
  set A : Matrix ι ι ℂ := (((k⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hA_def
  have hA' : Aᴴ * M.P w * A = M.P w := hA
  simp only [invApply]
  rw [← hA_def, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA']

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem continuous_wlen_invApply {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (c : InfinitePlace E → ℝ) (y : InfinitePlace E → ι → ℂ) :
    Continuous fun g : archUnitary h v => wlen M c (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  unfold wlen
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => ?_)
  exact continuous_const.mul (Complex.continuous_re.comp
    ((continuous_star.comp (hw w)).dotProduct (continuous_const.matrix_mulVec (hw w))))

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in
theorem measurableSet_wbelow {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (c : InfinitePlace E → ℝ) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    MeasurableSet {g : archUnitary h v | wlen M c (invApply g y) < t} :=
  (isOpen_lt (continuous_wlen_invApply M c y) continuous_const).measurableSet

theorem wUnfoldingTorus (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v)
    (M : Majorant h v) (c : InfinitePlace E → ℝ) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure]
    (D : ℕ) (La : AddSubgroup W) (x₀ : W) (hLa : IsDIntegral h D La) (hx₀ : x₀ ∈ La) (hne : x₀ ≠ 0)
    (hiso : h.toSesq x₀ x₀ = 0) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧ c₀ < ⊤ ∧ ∀ FD : Set (archUnitary h v),
      IsFundamentalDomain (vecStabGroup h v La x₀) FD μ → ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < t}) =
          c₀ * ∫⁻ b : InfinitePlace E → ℂ,
            {b : InfinitePlace E → ℂ | wlen M c (fun w => b w • vecAt v x₀ w) < t}.indicator
              (fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) b := by
  obtain ⟨ν, κ, τ, hν, -, hκ, hτm, hτ, hμ⟩ := h₂ M μ x₀ hne hiso
  obtain ⟨FD₀, hFD₀, h0, htop⟩ := h₃ D La x₀ hLa hx₀ hne hiso ν hν
  refine ⟨ν FD₀, h0, htop, fun FD hFD t ht => ?_⟩
  set y₀ := vecAt v x₀ with hy₀
  set wt : (InfinitePlace E → ℂ) → ℝ≥0∞ := fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))
    with hwt
  set S := {g : archUnitary h v | wlen M c (invApply g y₀) < t} with hS_def
  set T := {b : InfinitePlace E → ℂ | wlen M c (fun w => b w • y₀ w) < t} with hT_def
  have hS : MeasurableSet S := measurableSet_wbelow M c y₀ t

  have : SecondCountableTopology (vecStabGroup h v La x₀) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let s : (InfinitePlace E → ℂ) × M.stab → archUnitary h v := fun y => τ y.1 * y.2
  have hwtm : Measurable wt :=
    Finset.measurable_prod _ fun w _ => (measurable_pi_apply w).enorm.pow_const _
  have hsm' : Measurable s := (hτm.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsm : Measurable fun p : vecFixGroup h v x₀ × ((InfinitePlace E → ℂ) × M.stab) =>
      (p.1 : archUnitary h v) * s p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul (hsm'.comp measurable_snd)
  have hform : ∀ f : archUnitary h v → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ =
      ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂((volume.withDensity wt).prod κ) := by
    intro f hf
    have hin : Measurable fun y => ∫⁻ x : vecFixGroup h v x₀, f (x * s y) ∂ν :=
      (hf.comp hsm).lintegral_prod_left'
    rw [hμ f hf, lintegral_prod _ hin.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hwtm hin.lintegral_prod_right']
    rfl

  have hf : Measurable (S.indicator (1 : archUnitary h v → ℝ≥0∞)) := measurable_one.indicator hS
  have hinv : ∀ x : vecFixGroup h v x₀, ∀ g,
      S.indicator (1 : archUnitary h v → ℝ≥0∞) (x * g) = S.indicator 1 g := by
    intro x g
    have hx : invApply (x : archUnitary h v) y₀ = y₀ := invApply_of_mem_vecFixGroup x.2
    simp only [hS_def, Set.indicator_apply, Set.mem_ofPred_eq, invApply_mul, hx, Pi.one_apply]
  have key := h₁ M μ (vecFixGroup h v x₀) ν ((volume.withDensity wt).prod κ) s hsm hform
    (vecStabGroup h v La x₀) (vecStabGroup_le_vecFixGroup h v La x₀) FD FD₀ hFD hFD₀ _ hf hinv
  rw [Set.inter_comm, ← Measure.restrict_apply hS, ← lintegral_indicator_one hS, key]
  congr 1

  have hmS : Measurable fun y => S.indicator (1 : archUnitary h v → ℝ≥0∞) (s y) := hf.comp hsm'
  rw [lintegral_prod _ hmS.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwtm hmS.lintegral_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_ne_zero (InfinitePlace E)] with b hb
  have hk : ∀ k : M.stab, S.indicator (1 : archUnitary h v → ℝ≥0∞) (s (b, k)) =
      T.indicator 1 b := by
    intro k
    simp only [s, Set.indicator_apply, hS_def, hT_def, Set.mem_ofPred_eq, invApply_mul, hτ b hb,
      wlen_invApply_of_mem_stab M c k.2, Pi.one_apply]
  simp only [Pi.mul_apply, hk, lintegral_const, measure_univ, mul_one]
  by_cases hbT : b ∈ T
  · simp [Set.indicator_of_mem hbT]
  · simp [Set.indicator_of_notMem hbT]

theorem wUnfoldingIntegral (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v)
    (M : Majorant h v) (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure]
    (D : ℕ) (La : AddSubgroup W) (x₀ : W) (hLa : IsDIntegral h D La) (hx₀ : x₀ ∈ La) (hne : x₀ ≠ 0)
    (hiso : h.toSesq x₀ x₀ = 0) (FD : Set (archUnitary h v))
    (hFD : IsFundamentalDomain (vecStabGroup h v La x₀) FD μ) :
    μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < 1}) < ⊤ ∧
      ∀ t : ℝ, 0 < t → μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < t}) =
        ENNReal.ofReal t ^ (2 * finrank ℚ F * (finrank E W - 1)) *
          μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < 1}) := by
  have : FiniteDimensional E W := v.finiteDimensional_of_finite
  obtain ⟨c₀, -, hc₀top, hc₀⟩ := wUnfoldingTorus h v h₁ h₂ h₃ M c μ D La x₀ hLa hx₀ hne hiso
  set y := vecAt v x₀ with hy
  set q : InfinitePlace E → ℝ := fun w => c w * (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re with hq_def
  have hq : ∀ w, 0 < q w := fun w => mul_pos (hc w)
    (Complex.pos_iff.mp ((M.posDef w).dotProduct_mulVec_pos (VecAtNeZero.proof v x₀ hne w))).1
  obtain ⟨C, -, hCtop, hC⟩ := TorusIntegralHomogeneous.full (InfinitePlace E) q hq (finrank E W - 2)

  obtain ⟨k, hk⟩ : ∃ k, finrank E W = k + 2 :=
    ⟨finrank E W - 2, by have := two_le_finrank_of_isotropic h hne hiso; omega⟩
  have hcard : Fintype.card (InfinitePlace E) = finrank ℚ F := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h2
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have hexp : (2 * (finrank E W - 2) + 2) * Fintype.card (InfinitePlace E) =
      2 * finrank ℚ F * (finrank E W - 1) := by
    rw [hcard, hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    ring

  have hset : ∀ t : ℝ, 0 < t → {b : InfinitePlace E → ℂ | wlen M c (fun w => b w • y w) < t} =
      {b | ∑ w, q w * ‖b w‖ ^ 2 < t ^ 2} := by
    intro t ht
    ext b
    simp only [Set.mem_ofPred_eq, wlen, Real.sqrt_lt' ht, re_form_smul, hq_def, mul_assoc]
  have hval : ∀ t : ℝ, 0 < t → μ (FD ∩ {g | wlen M c (invApply g y) < t}) =
      c₀ * (C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1)))) := by
    intro t ht
    rw [hc₀ FD hFD t ht, hset t ht, hC t ht, hexp]
  have h1 := hval 1 one_pos
  rw [one_pow, ENNReal.ofReal_one, mul_one] at h1
  refine ⟨by rw [h1]; exact ENNReal.mul_lt_top hc₀top hCtop, fun t ht => ?_⟩
  rw [hval t ht, h1, ENNReal.ofReal_pow ht.le]
  ring

end OneSpace

theorem haarParabolicCoordinates_closed {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.of_open h v (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) (TorusEmbedding.full h v)
      (LineEigenvalue.closed h v) (TorusModulus.full h v) (SemidirectHaar.proof _ _) (UnitsInvHaar.proof _))

theorem stabilizerCovolumeFinite_closed {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) : StabilizerCovolumeFinite.Statement h v :=
  StabilizerCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun _ _ _ _ h _ v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (TorusEmbedding.full h v) (LineEigenvalue.closed h v) (TorusModulus.full h v)
      (SemidirectHaar.proof _ _) (UnitsInvHaar.proof _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun _ _ _ _ h _ v => UnipotentCocompact.proof h v (UnipotentCoordProper.proof h v)
      (UnipotentHorizontal.full h v) (UnipotentCentral.full h v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v)
    (UnipotentCocompact.proof h v (UnipotentCoordProper.proof h v) (UnipotentHorizontal.full h v)
      (UnipotentCentral.full h v))

theorem wUnfoldingIntegral_closed {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (M : Majorant h v) (c : InfinitePlace E → ℝ) (hc : ∀ w, 0 < c w)
    (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure]
    (D : ℕ) (La : AddSubgroup W) (x₀ : W) (hLa : IsDIntegral h D La) (hx₀ : x₀ ∈ La) (hne : x₀ ≠ 0)
    (hiso : h.toSesq x₀ x₀ = 0) (FD : Set (archUnitary h v))
    (hFD : IsFundamentalDomain (vecStabGroup h v La x₀) FD μ) :
    μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < 1}) < ⊤ ∧
      ∀ t : ℝ, 0 < t → μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < t}) =
        ENNReal.ofReal t ^ (2 * finrank ℚ F * (finrank E W - 1)) *
          μ (FD ∩ {g | wlen M c (invApply g (vecAt v x₀)) < 1}) :=
  wUnfoldingIntegral h v (fun _ => UnfoldAlongSubgroup.proof _ _) (haarParabolicCoordinates_closed h v)
    (stabilizerCovolumeFinite_closed h v) M c hc μ D La x₀ hLa hx₀ hne hiso FD hFD

end First

section IndefiniteRowSideFullHecke

open GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison
open GroundTheory.Heights₂.Heights.FiniteCovolume.HermitianSpaceComparison.Unfolding

attribute [local instance] archMulAction

variable {F : Type*} {E : Type} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E] [IsCMField E]
variable {W : Type u} [AddCommGroup W] [Module E W] {N : ℕ}
variable (h : HermitianForm F E W) (v : Basis (Fin N) E W)

theorem wNorm_majOf (M : Majorant h v) (c : InfinitePlace E → ℝ) (y : InfinitePlace E → Fin N → ℂ) :
    wlen M c y = wNorm (majOf M) c y := by
  unfold wlen wNorm
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  simp only [majOf, ReciprocityTheory.ChartRestriction.G.SA.hf, dotProduct, mulVec, Matrix.transpose_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def]
  ring

theorem lintegral_wBelowInd (M : Majorant h v) (c : InfinitePlace E → ℝ) (μ : Measure (archUnitary h v))
    (x₀ : W) (s : Set (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v))) (t : ℝ) :
    ∫⁻ g in s, wBelowInd (majOf M) c (v.equivFun x₀) t g ∂(μ.map (realMeas h v)) =
      μ (realMeas h v ⁻¹' s ∩ {g | wlen M c (invApply g (vecAt v x₀)) < t}) := by
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
  have hfun : ∀ g, wBelowInd (majOf M) c (v.equivFun x₀) t (realMeas h v g) =
      {g : archUnitary h v | wlen M c (invApply g (vecAt v x₀)) < t}.indicator 1 g := by
    intro g
    simp only [wBelowInd, Set.indicator_apply, Set.mem_ofPred_eq, realMeas_apply, wNorm_majOf,
      invApply.equiv, vecAt.equiv, Pi.one_apply]
  have hm : MeasurableSet {g : archUnitary h v | wlen M c (invApply g (vecAt v x₀)) < t} :=
    measurableSet_wbelow M c (vecAt v x₀) t
  simp_rw [hfun]
  rw [lintegral_indicator_one hm, Measure.restrict_apply hm, Set.inter_comm]

theorem unfolding_hermitian_lattice :
    ∀ (M' : IndefiniteRowSideFullHecke.FiniteCovolume.Majorant (divisionPairOfAdelicFormsFaceColumnsData h v)) (c : InfinitePlace E → ℝ), (∀ w, 0 < c w) →
    ∀ (L : Submodule (𝓞 E) (Fin N → E)) (v₀ : Fin N → E),
    IndefiniteRowSideFullHecke.FiniteCovolume.IsLattice L → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((divisionPairOfAdelicFormsFaceColumnsData h v).h x y)) →
    v₀ ∈ L → v₀ ≠ 0 → (divisionPairOfAdelicFormsFaceColumnsData h v).h v₀ v₀ = 0 →
    ∀ μ : Measure (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)), μ.IsHaarMeasure →
    ∃ s : Set (IndefiniteRowSideFullHecke.FiniteCovolume.RealPts (divisionPairOfAdelicFormsFaceColumnsData h v)), MeasurableSet s ∧
      IsFundamentalDomain (IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L v₀) s μ ∧
      (∫⁻ g in s, wBelowInd M' c v₀ 1 g ∂μ) < ⊤ ∧
      ∀ t : ℝ, 0 < t → (∫⁻ g in s, wBelowInd M' c v₀ t g ∂μ) =
        ENNReal.ofReal t ^ (2 * IndefiniteRowSideFullHecke.FiniteCovolume.fDeg E * (N - 1)) *
          ∫⁻ g in s, wBelowInd M' c v₀ 1 g ∂μ := by
  intro M' c hc L v₀ hL hint hv₀ hne hiso μ' hμ'
  obtain ⟨M, rfl⟩ := (Majorant.equiv (h := h) (v := v)).2 M'
  obtain ⟨x₀, rfl⟩ := v.equivFun.surjective v₀

  have hD : IndefiniteRowSideFullHecke.FiniteCovolume.IsDIntegral (divisionPairOfAdelicFormsFaceColumnsData h v)
      (L.toAddSubgroup.relIndex (IndefiniteRowSideFullHecke.FiniteCovolume.dual (divisionPairOfAdelicFormsFaceColumnsData h v) L).toAddSubgroup) L :=
    ⟨hL, hint, le_rfl⟩
  have hLa := (IsDIntegral.equiv_of_dualIndexFinite (DualIndexFinite.proof h) _ L).2 hD
  have hne' : x₀ ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  have hiso' : h.toSesq x₀ x₀ = 0 := by
    rw [← HermSpace.h.equiv h v]
    exact hiso
  have := isHaarMeasure_map_realMeas_symm h v μ'
  have hμ : (μ'.map (realMeas h v).symm).map (realMeas h v) = μ' := MeasurableEquiv.map_map_symm _

  obtain ⟨FD, hFDm, hFD⟩ := DiscreteFundamentalDomain.proof (archUnitary h v)
    (μ'.map (realMeas h v).symm) _ (vecStabGroup_discrete h v (latOf v L) hLa.isLattice x₀)
  have hs : IsFundamentalDomain (IndefiniteRowSideFullHecke.FiniteCovolume.gammaVecInf (divisionPairOfAdelicFormsFaceColumnsData h v) L (v.equivFun x₀))
      (realMeas h v '' FD) ((μ'.map (realMeas h v).symm).map (realMeas h v)) := by
    refine hFD.image_of_equiv (realMeas h v).toEquiv ?_ (vecStabEquiv h v L x₀).symm.toEquiv
      (fun g x => realMeas_semiconj h v L x₀ g x)
    have := ((realMeas h v).symm.measurable.measurePreserving
      ((μ'.map (realMeas h v).symm).map (realMeas h v)))
    rw [MeasurableEquiv.map_symm_map] at this
    exact this.quasiMeasurePreserving
  rw [hμ] at hs
  obtain ⟨h1, h2⟩ := wUnfoldingIntegral_closed h v M c hc (μ'.map (realMeas h v).symm) _ (latOf v L) x₀
    hLa hv₀ hne' hiso' FD hFD
  refine ⟨_, (realMeas h v).measurableSet_image.2 hFDm, hs, ?_⟩
  rw [← hμ]
  simp only [lintegral_wBelowInd, MeasurableEquiv.preimage_image]
  refine ⟨h1, fun t ht => ?_⟩
  rw [h2 t ht, exponent_eq (F := F) v]

end IndefiniteRowSideFullHecke

theorem WeightedUnfoldingIntegral.full : WeightedUnfoldingIntegral.Statement := by
  intro E _ _ _ N V
  have := unfolding_hermitian_lattice (FiniteCovolume.HermitianSpaceComparison.hermitianFormOfMatrix (maximalRealSubfield E) V)
    (Pi.basisFun E (Fin N))
  rwa [FiniteCovolume.HermitianSpaceComparison.matrixHermSpace_surjective] at this

end GroundTheory.Heights₂.Heights.NineStatements
