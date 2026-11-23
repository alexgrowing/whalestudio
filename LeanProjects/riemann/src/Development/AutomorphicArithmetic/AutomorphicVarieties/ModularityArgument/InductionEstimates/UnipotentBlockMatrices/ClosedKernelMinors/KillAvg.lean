import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusDifference

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open Classical in
private theorem finsum_eq_sum_filter {Q : Type} (f : Q → ℂ) (S : Set Q) (T : Finset Q) (hT : ∀ q, f q ≠ 0 → q ∈ T) :
    ∑ᶠ q ∈ S, f q = ∑ q ∈ T.filter (· ∈ S), f q := by
  refine finsum_mem_eq_sum_of_inter_support_eq f ?_
  ext q
  simp only [mem_inter_iff, Function.mem_support, Finset.coe_filter, mem_setOf_eq]
  exact ⟨fun h => ⟨⟨hT q h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

private theorem one_dir {K : Type} [Field K] [NumberField K] {n r : ℕ} {Q : Type} (f : Q → (UPos n r → 𝔸[K]) → ℂ)
    (hf : ∀ q, Continuous (f q)) (hfin : ∀ C, IsCompact C → {q | ∃ X ∈ C, f q X ≠ 0}.Finite) (S : Set Q)
    (hper : ∀ ξ ∈ unipLattice K n r, ∃ σ : Q → Q, BijOn σ S S ∧ ∀ q X, f q (ξ + X) = f (σ q) X)
    (e : 𝔸[K] → UPos n r → 𝔸[K]) (he : Continuous e)
    (hd : ∀ q ∈ S, ∀ X, ∫ y in GroundTheory.Global.fundamentalSet K, f q (X + e y) ∂GroundTheory.Global.adeleMeasure K = 0) :
    ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q X ∂unipMeasure K n r = 0 := by
  classical
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨B, hB, hEB⟩ : ∃ B, IsCompact B ∧ GroundTheory.Global.fundamentalSet K ⊆ B :=
    ⟨closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ _,
      (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod (GroundTheory.Global.isCompact_integralFiniteAdeles K),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hadd : Continuous fun p : 𝔸[K] × (UPos n r → 𝔸[K]) => p.2 + e p.1 := continuous_snd.add (he.comp continuous_fst)
  have hT := hfin _ ((hB.prod hC).image hadd)
  have hshift : ∀ y, ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q (X + y) ∂unipMeasure K n r =
      ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q X ∂unipMeasure K n r := by
    intro y
    refine setIntegral_add_right_of_periodic isAddFundamentalDomain_unipFundamentalDomain
      (h := fun X => ∑ᶠ q ∈ S, f q X) (fun ξ hξ s => ?_) y
    obtain ⟨σ, hσ, h⟩ := hper ξ hξ
    exact finsum_mem_eq_of_bijOn σ hσ fun q _ => h q s
  have hint : ∀ q, Integrable (Function.uncurry fun y X => f q (X + e y))
      (((GroundTheory.Global.adeleMeasure K).restrict (GroundTheory.Global.fundamentalSet K)).prod
        ((unipMeasure K n r).restrict (unipFundamentalDomain K n r))) := by
    intro q
    rw [Measure.prod_restrict]
    exact (((hf q).comp hadd).continuousOn.integrableOn_compact (hB.prod hC)).mono_set (prod_mono hEB hDC)
  have hint1 : ∀ q y, IntegrableOn (fun X => f q (X + y)) (unipFundamentalDomain K n r) (unipMeasure K n r) := fun q y =>
    (((hf q).comp (continuous_add_const y)).continuousOn.integrableOn_compact hC).mono_set hDC
  calc ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q X ∂unipMeasure K n r
      = ∫ _y in GroundTheory.Global.fundamentalSet K,
          ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q X ∂unipMeasure K n r ∂GroundTheory.Global.adeleMeasure K := by
        rw [setIntegral_const, Measure.real, GroundTheory.Global.adeleMeasure_fundamentalSet]; simp
    _ = ∫ y in GroundTheory.Global.fundamentalSet K, ∑ q ∈ hT.toFinset.filter (· ∈ S),
          ∫ X in unipFundamentalDomain K n r, f q (X + e y) ∂unipMeasure K n r ∂GroundTheory.Global.adeleMeasure K := by
        refine setIntegral_congr_fun (GroundTheory.Global.measurableSet_fundamentalSet K) fun y hy => ?_
        show _ = ∑ q ∈ hT.toFinset.filter (· ∈ S), ∫ X in unipFundamentalDomain K n r, f q (X + e y) ∂unipMeasure K n r
        rw [← integral_finsetSum _ fun q _ => hint1 q (e y), ← hshift (e y)]
        refine setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X hX => ?_
        refine finsum_eq_sum_filter (fun q => f q (X + e y)) S _ fun q hq => ?_
        exact hT.mem_toFinset.2 ⟨_, ⟨(y, X), ⟨hEB hy, hDC hX⟩, rfl⟩, hq⟩
    _ = 0 := by
        refine (integral_finsetSum _ fun q _ => (hint q).integral_prod_left).trans ?_
        refine Finset.sum_eq_zero fun q hq => ?_
        refine (integral_integral_swap (hint q)).trans ?_
        simp only [hd q (Finset.mem_filter.1 hq).2, integral_zero]

private theorem many_dir {K : Type} [Field K] [NumberField K] {n r : ℕ} {Q J : Type} (f : Q → (UPos n r → 𝔸[K]) → ℂ)
    (hf : ∀ q, Continuous (f q)) (hfin : ∀ C, IsCompact C → {q | ∃ X ∈ C, f q X ≠ 0}.Finite) (S : Set Q) (c : Q → J)
    (h : ∀ a, ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ {q | q ∈ S ∧ c q = a}, f q X ∂unipMeasure K n r = 0) :
    ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S, f q X ∂unipMeasure K n r = 0 := by
  classical
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hT := hfin _ hC
  have key : ∀ S' : Set Q, ∫ X in unipFundamentalDomain K n r, ∑ᶠ q ∈ S', f q X ∂unipMeasure K n r =
      ∑ q ∈ hT.toFinset.filter (· ∈ S'), ∫ X in unipFundamentalDomain K n r, f q X ∂unipMeasure K n r := by
    intro S'
    rw [← integral_finsetSum _ fun q _ => (((hf q).continuousOn.integrableOn_compact hC).mono_set hDC)]
    refine setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X hX => ?_
    exact finsum_eq_sum_filter (fun q => f q X) S' _ fun q hq => hT.mem_toFinset.2 ⟨_, hDC hX, hq⟩
  rw [key, ← Finset.sum_fiberwise_of_maps_to (g := c) (t := (hT.toFinset.filter (· ∈ S)).image c)
    fun q hq => Finset.mem_image_of_mem c hq]
  refine Finset.sum_eq_zero fun a _ => ?_
  have := h a
  rw [key] at this
  rw [Finset.filter_filter]
  convert this using 2
  ext q
  simp

private noncomputable def act {K : Type} [Field K] [NumberField K] (η : Gam K (2 + 2)) (q : Cos K) : Cos K :=
  Quotient.mk _ (q.out * η)

private theorem act_mk {K : Type} [Field K] [NumberField K] (η γ : Gam K (2 + 2)) :
    act η (Quotient.mk _ γ) = Quotient.mk _ (γ * η) := by
  have h : (QuotientGroup.rightRel (ParΓ K 2 2)) (Quotient.mk (QuotientGroup.rightRel (ParΓ K 2 2)) γ).out γ :=
    Quotient.exact (Quotient.out_eq _)
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  have h' := QuotientGroup.rightRel_apply.1 h
  rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]

private theorem act_act {K : Type} [Field K] [NumberField K] (η η' : Gam K (2 + 2)) (h : η * η' = 1) (q : Cos K) :
    act η' (act η q) = q := by
  rw [show act η q = Quotient.mk _ (q.out * η) from rfl, act_mk, mul_assoc, h, mul_one, Quotient.out_eq]

private theorem act_val {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ)
    (hF : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (η : Gam K (2 + 2)) (q : Cos K) (x : G1 K (2 + 2)) :
    F (((act η q).out : G1 K (2 + 2)) * x) = F ((q.out : G1 K (2 + 2)) * (η * x)) := by
  obtain ⟨δ, hδ, h⟩ := (pkLaws (K := K)).2.2.2 (q.out * η)
  rw [show act η q = Quotient.mk _ (q.out * η) from rfl, h, mul_assoc, hF δ hδ, Subgroup.coe_mul, mul_assoc]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.killAvg :
    ∀ {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F → ∀ (r : ℕ) (S : Set (Cos K)),
      (∀ (γ γ' : Gam K (2 + 2)) (ξ : unipLattice K (2 + 2) r), (γ' : G1 K (2 + 2)) = γ * unipOne K (2 + 2) r ξ.1 →
        (Quotient.mk _ γ : Cos K) ∈ S → (Quotient.mk _ γ' : Cos K) ∈ S) →
      (∀ q ∈ S, ∃ X₀, Dies F r (q.out : G1 K (2 + 2)) X₀) → ∀ g,
        ∫ X in unipFundamentalDomain K (2 + 2) r, ∑ᶠ q ∈ S, F ((q.out : G1 K (2 + 2)) * (unipOne K (2 + 2) r X * g)) ∂unipMeasure K (2 + 2) r = 0 := by
  intro K _ _ F hFc hF hband r S hS hD g
  classical
  obtain ⟨R, hR⟩ := hband
  let u : unipLattice K (2 + 2) r → Gam K (2 + 2) := fun ξ => ⟨unipOne K (2 + 2) r ξ.1, unipOne_mem_rationalGLOne r ξ⟩
  have hu : ∀ ξ, u ξ * u (-ξ) = 1 := fun ξ => Subtype.ext (by
    show unipOne K (2 + 2) r ξ.1 * unipOne K (2 + 2) r (-ξ.1) = 1
    rw [← unipOne_add, add_neg_cancel, unipOne_zero])
  have hu' : ∀ ξ, u (-ξ) * u ξ = 1 := fun ξ => by simpa using hu (-ξ)
  have hSa : ∀ ξ q, q ∈ S → act (u ξ) q ∈ S := fun ξ q hq =>
    hS q.out (q.out * u ξ) ξ rfl (by rwa [Quotient.out_eq])
  have hDa : ∀ ξ (q : Cos K) a, Dies F r (q.out : G1 K (2 + 2)) a → Dies F r ((act (u ξ) q).out : G1 K (2 + 2)) a := by
    intro ξ q a h x
    rw [← h (unipOne K (2 + 2) r ξ.1 * x)]
    congr 1
    funext y
    rw [mul_assoc, act_val F hF, mul_assoc]
    congr 2
    show unipOne K (2 + 2) r ξ.1 * _ = _
    rw [← mul_assoc, ← mul_assoc, ← unipOne_add, ← unipOne_add, add_comm ξ.1]
  let c : Cos K → UPos (2 + 2) r → K := fun q => Classical.epsilon fun a => Dies F r (q.out : G1 K (2 + 2)) a
  have hc : ∀ ξ q, c (act (u ξ) q) = c q := by
    intro ξ q
    refine congrArg Classical.epsilon (funext fun a => propext ⟨fun h => ?_, hDa ξ q a⟩)
    have := hDa (-ξ) _ a h
    rwa [act_act _ _ (hu ξ)] at this
  have hcont : Continuous fun X => unipOne K (2 + 2) r X * g := (continuous_unipOne r).mul continuous_const
  have hf : ∀ q : Cos K, Continuous fun X => F ((q.out : G1 K (2 + 2)) * (unipOne K (2 + 2) r X * g)) :=
    fun q => hFc.comp (continuous_const.mul hcont)
  have hfin : ∀ C, IsCompact C →
      {q : Cos K | ∃ X ∈ C, F ((q.out : G1 K (2 + 2)) * (unipOne K (2 + 2) r X * g)) ≠ 0}.Finite := by
    intro C hC
    refine (locFin _ (-R) (hC.image hcont)).subset ?_
    rintro q ⟨X, hX, h⟩
    exact ⟨_, ⟨X, hX, rfl⟩, (abs_le.1 (hR _ h)).1⟩
  refine many_dir _ hf hfin S c fun a => ?_
  have hm : ∀ ξ, MapsTo (act (u ξ)) {q | q ∈ S ∧ c q = a} {q | q ∈ S ∧ c q = a} :=
    fun ξ q hq => ⟨hSa ξ q hq.1, (hc ξ q).trans hq.2⟩
  have hb : ∀ ξ, BijOn (act (u ξ)) {q | q ∈ S ∧ c q = a} {q | q ∈ S ∧ c q = a} := fun ξ =>
    Set.InvOn.bijOn (f' := act (u (-ξ)))
      ⟨fun q _ => act_act _ _ (hu ξ) q, fun q _ => act_act _ _ (hu' ξ) q⟩ (hm ξ) (hm (-ξ))
  refine one_dir _ hf hfin _ (fun ξ hξ => ⟨act (u ⟨ξ, hξ⟩), hb _, fun q X => ?_⟩)
    (fun y p => y * algebraMap K 𝔸[K] (a p)) (continuous_pi fun p => continuous_id.mul continuous_const) ?_
  · rw [act_val F hF, unipOne_add, mul_assoc]
  · rintro q ⟨hq, rfl⟩ X
    have h : Dies F r (q.out : G1 K (2 + 2)) (c q) := Classical.epsilon_spec (hD q hq)
    rw [← h (unipOne K (2 + 2) r X * g)]
    congr 1
    funext y
    rw [add_comm X, unipOne_add, mul_assoc, mul_assoc]
