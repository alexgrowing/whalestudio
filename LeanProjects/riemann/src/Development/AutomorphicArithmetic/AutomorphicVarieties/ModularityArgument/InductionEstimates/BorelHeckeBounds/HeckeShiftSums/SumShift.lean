import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

private theorem mk_shift {G : Type*} [Group G] (P : Subgroup G) (a b : G) :
    (Quotient.mk (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out * b)) =
      Quotient.mk (QuotientGroup.rightRel P) (a * b) := by
  have h : (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out) a :=
    Quotient.mk_out (s := QuotientGroup.rightRel P) a
  refine Quotient.sound ?_
  change (QuotientGroup.rightRel P) _ _
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

private theorem shift_bij {G : Type*} [Group G] (P : Subgroup G) (b : G) :
    Function.Bijective fun q : Quotient (QuotientGroup.rightRel P) =>
      Quotient.mk (QuotientGroup.rightRel P) (q.out * b) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun q => Quotient.mk (QuotientGroup.rightRel P) (q.out * b⁻¹), fun q => ?_, fun q => ?_⟩
  · simp only [mk_shift, mul_inv_cancel_right, Quotient.out_eq]
  · simp only [mk_shift, inv_mul_cancel_right, Quotient.out_eq]

variable {K : Type} [Field K] [NumberField K]

private theorem sum_shift {M : Type*} [AddCommMonoid M] (F : G1 K (2 + 2) → M)
    (hP : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (γ : G1 K (2 + 2)) (hγ : γ ∈ Gam K (2 + 2))
    (g : G1 K (2 + 2)) :
    ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * (γ * g)) = ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * g) := by
  have hout : ∀ (c : Gam K (2 + 2)) (g : G1 K (2 + 2)),
      F ((((Quotient.mk _ c : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * g) = F (c * g) := fun c g => by
    obtain ⟨δ, hδ, h⟩ := (pkLaws (K := K)).2.2.2 c
    rw [h, mul_assoc, hP δ hδ]
  refine finsum_eq_of_bijective _ (shift_bij (ParΓ K 2 2) ⟨γ, hγ⟩) fun q => ?_
  rw [hout, Subgroup.coe_mul, mul_assoc]

private theorem desc_cont {Y : Type*} [TopologicalSpace Y] (f : G1 K (2 + 2) → Y) (hc : Continuous f)
    (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    Continuous fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  rw [(isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.continuous_iff]
  have : (fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y)) ∘ mk (Gam K (2 + 2)) = f := funext fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K (2 + 2)) (g := (mk (Gam K (2 + 2)) g).out) (h := g)).1 (Quotient.out_eq _)
    change f _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  rwa [this]

private theorem desc_sm {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (f : G1 K (2 + 2) → Y) (hc : Continuous f) (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  exact (desc_cont f hc hi).stronglyMeasurable

private noncomputable def ramp (T : ℝ) (n : ℕ) (h : ℝ) : ℝ := max 0 (min 1 (((n : ℝ) + 1) * (h - T)))

private theorem ramp_cont (T : ℝ) (n : ℕ) : Continuous (ramp T n) := by
  unfold ramp
  fun_prop

private theorem ramp_zero {T h : ℝ} (n : ℕ) (hh : h ≤ T) : ramp T n h = 0 := by
  have : ((n : ℝ) + 1) * (h - T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hh)
  exact max_eq_left ((min_le_right _ _).trans this)

private theorem ramp_lim (T h : ℝ) :
    Tendsto (fun n : ℕ => ((ramp T n h : ℝ) : ℂ)) atTop (𝓝 (if T < h then 1 else 0)) := by
  split_ifs with hh
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (h - T))
    have hp : 0 < h - T := sub_pos.2 hh
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : 1 ≤ ((n : ℝ) + 1) * (h - T) := by
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ hp] at hN
      nlinarith
    have : ramp T n h = 1 := by
      unfold ramp
      rw [min_eq_left h1]
      exact max_eq_right zero_le_one
    rw [this]
    simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [ramp_zero n (not_lt.1 hh)]
    simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kT :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)) (T : ℝ), ∃ kk : G1 K (2 + 2) → L2 μ,
      (∀ x φ, ⟪kk x, φ⟫_ℂ = lam T (rc μ a φ) x) ∧ (∀ γ ∈ Gam K (2 + 2), ∀ x, kk (γ * x) = kk x) ∧ (∀ x, Om T x → kk x = kv μ a x) ∧
      StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => kk (Quotient.out y) := by
  intro K _ _ μ _ a T
  obtain ⟨kc, hkc, hin⟩ := (ctKv μ a).1 2
  have hlaw := (ctKv μ a).2
  have hH := hpSpec (K := K)
  have hkP : ∀ γ ∈ PK K, ∀ z, kc (γ * z) = kc z := fun γ hγ z =>
    ext_inner_right ℂ fun φ => by rw [hin, hin, (hlaw φ).2.2.2.1 γ hγ z]

  let A : (ℝ → ℂ) → G1 K (2 + 2) → L2 μ := fun w x =>
    kv μ a x - ∑ᶠ q : Cos K, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)
  have hAinv : ∀ w, ∀ γ ∈ Gam K (2 + 2), ∀ x, A w (γ * x) = A w x := fun w γ hγ x => by
    have h1 := (ropAe K (2 + 2) μ a).2 γ hγ x
    have h2 := sum_shift (K := K) (fun g => w (HH g) • kc g)
      (fun δ hδ g => by simp only [hkP δ hδ g, hH.2.2.1 δ hδ g]) γ hγ x
    simp only [A, h1, h2]
  let ind : ℝ → ℂ := fun h => if T < h then 1 else 0

  have hfin : ∀ x : G1 K (2 + 2), {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)}.Finite := fun x =>
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, hq⟩
  have hsupp : ∀ (w : ℝ → ℂ), (∀ h, h < T → w h = 0) → ∀ x : G1 K (2 + 2),
      (Function.support fun q : Cos K => w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)) ⊆
        {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)} := fun w hw x q hq => by
    by_contra hlt
    exact hq (by beta_reduce; rw [hw _ (not_le.1 hlt), zero_smul])
  have hind : ∀ h, h < T → ind h = 0 := fun h hh => if_neg (not_lt.2 hh.le)
  have hrz : ∀ n : ℕ, ∀ h, h < T → ((ramp T n h : ℝ) : ℂ) = 0 := fun n h hh => by
    rw [ramp_zero n hh.le]
    simp
  refine ⟨A ind, fun x φ => ?_, hAinv ind, fun x hx => ?_, ?_⟩
  · let ip : L2 μ →+ ℂ :=
      { toFun := fun v => ⟪v, φ⟫_ℂ, map_zero' := inner_zero_left _, map_add' := fun u v => inner_add_left _ _ _ }
    have hsum : ⟪∑ᶠ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ =
        ∑ᶠ q : Cos K, ⟪ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ :=
      ip.map_finsum ((hfin x).subset (hsupp ind hind x))
    simp only [A, inner_sub_left, inner_kv, hsum, lam, th, hi]
    congr 1
    refine finsum_congr fun q => ?_
    rw [inner_smul_left, hin]
    by_cases h : T < HH ((q.out : G1 K (2 + 2)) * x)
    · simp [ind, h]
    · simp [ind, h]
  · have : ∀ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) = 0 := fun q => by
      have : ind (HH ((q.out : G1 K (2 + 2)) * x)) = 0 := if_neg (not_lt.2 (hx q))
      rw [this, zero_smul]
    simp only [A, this, finsum_zero, sub_zero]
  ·
    have hcont : ∀ n : ℕ, Continuous (A fun h => ((ramp T n h : ℝ) : ℂ)) := fun n => by
      refine (kvCont K (2 + 2) μ a).sub (continuous_finsum (fun q => ?_) fun x => ?_)
      · have hm : Continuous fun x : G1 K (2 + 2) => (q.out : G1 K (2 + 2)) * x :=
          continuous_const.mul continuous_id
        exact (Complex.continuous_ofReal.comp ((ramp_cont T n).comp (hH.2.2.2.1.comp hm))).smul (hkc.comp hm)
      · obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
        refine ⟨C, hx, (locFin C T hC).subset fun q ⟨g, hg, hgC⟩ => ⟨g, hgC, ?_⟩⟩
        exact hsupp _ (hrz n) g hg
    have hdesc : ∀ n : ℕ, StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) =>
        A (fun h => ((ramp T n h : ℝ) : ℂ)) (Quotient.out y) := fun n =>
      desc_sm (A fun h => ((ramp T n h : ℝ) : ℂ)) (hcont n) (hAinv fun h => ((ramp T n h : ℝ) : ℂ))
    refine stronglyMeasurable_of_tendsto atTop hdesc (tendsto_pi_nhds.2 fun y => ?_)
    set x : G1 K (2 + 2) := Quotient.out y
    have e : ∀ w : ℝ → ℂ, (∀ h, h < T → w h = 0) →
        A w x = kv μ a x - ∑ q ∈ (hfin x).toFinset, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) := fun w hw => by
      simp only [A]
      rw [finsum_eq_sum_of_support_subset (s := (hfin x).toFinset) _ (by rw [Set.Finite.coe_toFinset]; exact hsupp w hw x)]
    simp only [e _ (hrz _), e ind hind]
    refine tendsto_const_nhds.sub (tendsto_finset_sum _ fun q _ => ?_)
    exact (ramp_lim T _).smul_const _
