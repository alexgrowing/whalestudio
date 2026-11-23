import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.OrthCt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

set_option synthInstance.maxHeartbeats 400000 in
private theorem intD {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) {E : Type} [NormedAddCommGroup E]
    {h : G1 K n → E} (hh : Continuous h) : Integrable h D.ν := by
  have := D.prob
  have h1 : IntegrableOn h (D.U : Set (G1 K n)) D.ν := hh.continuousOn.integrableOn_compact (typeFin D).1
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at h1

private theorem intR {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (w : L2 μ) : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k w) D.ν :=
  intD D (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit w))

private theorem fixClosed {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧ ∀ w, w ∈ S ↔ D.FixedByTypeProjector μ w := by
  let T₀ : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := fun w => ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν
      map_add' := fun a b => by
        rw [← integral_add (intR D μ a) (intR D μ b)]
        simp only [map_add, smul_add]
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  have hb : ∀ w, ‖T₀ w‖ ≤ (∫ k, ‖D.e k‖ ∂D.ν) * ‖w‖ := by
    intro w
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_mul_const]
    congr 1
    ext k
    rw [norm_smul, UnitaryRep.norm_map]
  let T : L2 μ →L[ℂ] L2 μ := T₀.mkContinuous _ hb
  refine ⟨LinearMap.eqLocus (T : L2 μ →ₗ[ℂ] L2 μ) LinearMap.id, isClosed_eq T.continuous continuous_id, fun w => Iff.rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
private theorem fixRep {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C)
    (hfix : D.Fix Φ) : D.FixedByTypeProjector μ v := by
  have := D.prob
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hQ := h.ae_eq_quotFun
  have hQc := continuous_quotFun h.2.1 h.1
  set Q := quotFun Φ h.2.1 with hQd
  have hQb : ∀ x, ‖Q x‖ ≤ C := fun x => by
    obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
    exact hC y
  refine ext_inner_left ℂ fun w => ?_
  have hw : Integrable (fun x => conj (w x)) (quotientMeasure (Gam K n) μ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp ((Lp.memLp w).integrable one_le_two)
  have hcoef : ∀ k, ⟪w, D.e k • rightRegularRep (Gam K n) μ k v⟫_ℂ =
      ∫ x, D.e k * conj (w x) * Q (rightMul (Gam K n) k x) ∂quotientMeasure (Gam K n) μ := by
    intro k
    rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
    have h2 : (fun x => v (rightMul (Gam K n) k x)) =ᵐ[quotientMeasure (Gam K n) μ]
        fun x => Q (rightMul (Gam K n) k x) :=
      (measurePreserving_rightMul μ k).quasiMeasurePreserving.ae_eq_comp hQ
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rightRegularRep (Gam K n) μ k v, h2] with x h3 h4
    rw [h3, h4, RCLike.inner_apply', mul_assoc]
  have hI : Integrable (Function.uncurry fun k x => D.e k * conj (w x) * Q (rightMul (Gam K n) k x))
      (D.ν.prod (quotientMeasure (Gam K n) μ)) := by
    have h0 : Integrable D.e D.ν := intD D D.cont
    have h1 : Integrable (fun p : G1 K n × RightCosetSpace (Gam K n) => D.e p.1 * conj (w p.2))
        (D.ν.prod (quotientMeasure (Gam K n) μ)) := Integrable.mul_prod (f := D.e) (g := fun x => conj (w x)) h0 hw
    have hc : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => Q (rightMul (Gam K n) p.1 p.2) := by
      have hr : Continuous fun p : RightCosetSpace (Gam K n) × G1 K n => rightMul (Gam K n) p.2 p.1 :=
        continuous_rightMul_prod (Gam K n)
      have h3 : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => (p.2, p.1) :=
        continuous_snd.prodMk continuous_fst
      have h4 := hr.comp h3
      have h5 := hQc.comp h4
      exact h5
    have h2 := Integrable.mul_bdd (c := C) h1 hc.aestronglyMeasurable (Eventually.of_forall fun p => hQb _)
    exact h2
  rw [← integral_inner (intR D μ v)]
  simp only [hcoef]
  rw [integral_integral_swap hI, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hQ] with x hx
  rw [RCLike.inner_apply', hx]
  obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
  simp only [rightMul_mk, hQd, quotFun_mk]
  rw [← hfix y, ← integral_const_mul]
  congr 1
  ext k
  ring

private theorem thFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) {F : G1 K (2 + 2) → ℂ}
    (hF : Continuous F)
    (hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite)
    (hfix : D.Fix F) : D.Fix (th F) := by
  intro g
  have hc : IsCompact ((fun k => g * k) '' (D.U : Set (G1 K (2 + 2)))) :=
    (typeFin D).1.image (continuous_const_mul g)
  have hS := hfin _ hc
  have hs : ∀ k ∈ D.U, th F (g * k) = ∑ q ∈ hS.toFinset, F ((q.out : G1 K (2 + 2)) * g * k) := by
    intro k hk
    simp only [mul_assoc]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Finite.coe_toFinset]
    exact ⟨g * k, ⟨k, hk, rfl⟩, hq⟩
  have h1 := hs 1 D.U.one_mem
  simp only [mul_one] at h1
  rw [h1, ← Finset.sum_congr rfl fun q _ => hfix ((q.out : G1 K (2 + 2)) * g), ← integral_finset_sum]
  · refine integral_congr_ae ?_
    filter_upwards [D.supp] with k hk
    rw [hs k hk, Finset.mul_sum]
  · intro q _
    exact intD D (D.cont.mul (hF.comp (continuous_const_mul _)))

private theorem bfFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) (β : ℝ → ℂ) {f : G1 K (2 + 2) → ℂ}
    (hfix : D.Fix f) : D.Fix (bf β f) := by
  intro g
  unfold bf
  rw [← hfix g, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [D.supp] with k hk
  have h1 : HP 2 2 (g * k) = HP 2 2 g := (hpSpec.2.1 k ((typeFin D).2.1 hk)).2 g
  rw [h1]
  ring

private theorem ctRep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) (r : ℕ)
    (h0 : ∀ g, ∫ X in unipFundamentalDomain K n r, Φ (unipOne K n r X * g) ∂unipMeasure K n r = 0) :
    constantTermL2 μ r v =ᵐ[μ] 0 := by
  filter_upwards [ae_ctFun_congr μ r h.ae_eq_quotFun] with y hy
  rw [constantTermL2, hy]
  exact h0 y

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctZero :
    CtZeroC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨S₀, hS₀, h₀⟩ := fixClosed D μ
  obtain ⟨S₁, hS₁, h₁⟩ := ctClosed μ 1
  obtain ⟨S₃, hS₃, h₃⟩ := ctClosed μ 3
  let S : Submodule ℂ (L2 μ) := (cuspidalL2 μ)ᗮ ⊓ (S₀ ⊓ (S₁ ⊓ S₃))
  have hS : IsClosed (S : Set (L2 μ)) :=
    (Submodule.isClosed_orthogonal _).inter (hS₀.inter (hS₁.inter hS₃))
  have hgen : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧
      ∀ᵐ x : ℝ, u x = β x • v} ≤ S.comap A.J.toLinearMap := by
    rw [Submodule.span_le]
    rintro u ⟨β, v, hβ, hβc, hu⟩
    have hrep : Reps μ (A.J u) (th (bf β (A.sec v))) := A.spec β v u hβ hβc hu
    obtain ⟨hsec, hfix⟩ := (A.onto (A.sec v)).1 ⟨v, rfl⟩
    obtain ⟨hp, hband, hdec⟩ := bfFun _ β (secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hsec hfix) hβ hβc
    obtain ⟨hfin, hcont, hinv, hb⟩ := thBasic μ _ hp.cont hp.rat hband
    obtain ⟨-, ⟨C, hC⟩, -⟩ := hb hdec
    have hcr : IsContRep μ (A.J u) (th (bf β (A.sec v))) := ⟨hcont, hinv, hrep⟩
    refine ⟨?_, (h₀ _).2 ?_, (h₁ _).2 ?_, (h₃ _).2 ?_⟩
    · refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
      exact orthCt μ _ hp.cont hp.rat hband hdec hp.unip _ w hrep (hw 2 (by norm_num) (by norm_num))
    · exact fixRep D μ hcr hC (thFix D hp.cont hfin (bfFix D β hfix))
    · exact ctRep μ hcr 1 fun g => (thCt _ hp hband g).1
    · exact ctRep μ hcr 3 fun g => (thCt _ hp hband g).2.1
  intro u
  have hu : A.J u ∈ S :=
    closure_minimal (s := _) (t := A.J ⁻¹' (S : Set (L2 μ))) hgen (hS.preimage A.J.continuous) ((denseCc d).1 u)
  obtain ⟨e, e₀, e₁, e₃⟩ := hu
  exact ⟨(Submodule.starProjection_apply_eq_zero_iff _).2 e, (h₀ _).1 e₀, (h₁ _).1 e₁, (h₃ _).1 e₃⟩
