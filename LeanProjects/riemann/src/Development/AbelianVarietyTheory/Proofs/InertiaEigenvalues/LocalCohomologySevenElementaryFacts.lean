import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing

noncomputable section

open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT NumberField IsDedekindDomain ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.LocElem

theorem padicInt_coeff {p : ℕ} [Fact p.Prime] : PadicCoeff p ℤ_[p] := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [isAdic_iff]
    have key : ∀ n : ℕ, ((IsLocalRing.maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ))) := by
      intro n
      ext x
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, SetLike.mem_coe,
        ← PadicInt.norm_le_pow_iff_mem_span_pow, mem_closedBall_zero_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · rw [key]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (show (1:ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt))
      refine ⟨n, ?_⟩
      rw [key]
      intro x hx
      apply hball
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt hx ?_
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact hn
  · rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem mulSub_open {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (hM : IsFGTop O M) (hO : PadicCoeff p O) {a : O} (ha : a ≠ 0) :
    IsOpen ((mulSub a M : Submodule O M) : Set M) := by
  have := hO.compact
  have := hO.ring
  have := hM.t2
  have := hM.csmul
  obtain ⟨s, hs⟩ := hM.fg.fg_top

  let f : (s → O) →ₗ[O] M := Fintype.linearCombination O (fun i : s => (i : M))
  have hfc : Continuous f := by
    show Continuous fun v : s → O => ∑ i, v i • (i : M)
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hs]
  have hq : Topology.IsQuotientMap f :=
    (hfc.isClosedMap).isQuotientMap hfc hfs

  have haO : IsOpen ((Ideal.span {a} : Ideal O) : Set O) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e : (Ideal.span {(u : O) * ϖ ^ n} : Ideal O) = IsLocalRing.maximalIdeal O ^ n := by
      rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
        hϖ.maximalIdeal_eq]
    rw [e]
    exact (isAdic_iff.1 hO.adic).1 n
  have hopen : IsOpen ((((mulSub a M).comap f).toAddSubgroup : AddSubgroup (s → O)) : Set (s → O)) := by
    refine AddSubgroup.isOpen_mono (H₁ := (Submodule.pi Set.univ fun _ => (Ideal.span {a} : Ideal O)).toAddSubgroup) ?_ ?_
    · intro v hv
      have : ∀ i, ∃ w : O, a * w = v i := fun i => by
        obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hv i (Set.mem_univ i))
        exact ⟨w, by rw [mul_comm]; exact hw⟩
      choose w hw using this
      refine ⟨f w, ?_⟩
      show a • f w = f v
      rw [← map_smul]
      congr 1
      funext i
      exact hw i
    · show IsOpen (Set.univ.pi fun _ => ((Ideal.span {a} : Ideal O) : Set O))
      exact isOpen_set_pi Set.finite_univ fun _ _ => haO
  rw [← hq.isOpen_preimage]
  exact hopen

theorem contAction_quotient {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V} (h : ReciprocityTheory.Gal.ContAction ρ)
    (T : Submodule O V) (hT : StableUnder ρ T) : ReciprocityTheory.Gal.ContAction (ρ.quotient T hT) := by
  have hq : IsOpenQuotientMap (Prod.map (id : G → G) T.mkQ) :=
    IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ T)
  unfold ReciprocityTheory.Gal.ContAction
  rw [hq.isQuotientMap.continuous_iff]
  exact continuous_quot_mk.comp h

theorem cup_eq_zero_of_coboundary {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {M T₂ P : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [AddCommGroup T₂] [Module O T₂] [TopologicalSpace T₂]
    [IsTopologicalAddGroup T₂] [ContinuousConstSMul O T₂] [AddCommGroup P] [Module O P]
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul O P]
    (ρM : Representation O Γ M) (ρ₂ : Representation O Γ T₂) (ρP : Representation O Γ P)
    (b : M →ₗ[O] T₂ →ₗ[O] P) (hb : Continuous fun q : M × T₂ => b q.1 q.2)
    (hbe : ∀ g x y, b (ρM g x) (ρ₂ g y) = ρP g (b x y)) (h₂ : ReciprocityTheory.Gal.ContAction ρ₂)
    (x : Z1 ρM) (t : Z1 ρ₂) (c : Γ → P) (hc : Continuous c)
    (hcz : ∀ g h, b (ρM g (x.1 h)) (t.1 g) = ρP g (c h) - c (g * h) + c g) :
    cupProductH1H1 ρM ρ₂ ρP b hb hbe h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show (Submodule.Quotient.mk (cupCocycleZ1Z1 ρM ρ₂ ρP b hb hbe h₂ x t) : H2 ρP) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -(b (x.1 g) (t.1 g)) - c g, ((hb.comp (x.2.1.prodMk t.2.1)).neg).sub hc, ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  have e := hcz g h
  simp only [d1_apply, Submodule.coe_subtype, cupCocycleZ1Z1_apply, map_sub, map_neg, ← hbe, x.2.2 g h, t.2.2 g h, map_add,
    LinearMap.add_apply]
  have e' : ρP g (c h) = b (ρM g (x.1 h)) (t.1 g) + c (g * h) - c g := by rw [e]; abel
  rw [e']
  abel

theorem pr_eq_zero_of_coboundary {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O) (hc : Continuous c)
    (hcz : ∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := by
  show D.inv (cupProductH1H1 D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') (Submodule.Quotient.mk x) (Submodule.Quotient.mk t)) = 0
  have h0 := cup_eq_zero_of_coboundary D.ρA D.ρTl' (twist D.ε (KO O)) (pairKO D.bT D.T) (pairKO_cont D.bT D.contbT D.T)
    D.pairKO_equiv (sub_contAction D.contT' _ D.stT') x t c hc (fun g k => hcz g k)
  exact (congrArg D.inv h0).trans (map_zero _)

theorem quotShape_of_equiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X]
    [Module O X] (Hc F Hc' F' : Submodule O X) (d : ℕ)
    (e : (Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype)) (h : QuotShape Hc F d) :
    QuotShape Hc' F' d := by
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := h
  refine ⟨Cy, i1, i2, e.toLinearMap ∘ₗ ι, π ∘ₗ e.symm.toLinearMap, e.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (e.symm y)]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [← hz, LinearEquiv.symm_apply_apply]⟩

theorem mem_integers_iff_norm_le_one {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 :=
  GlobalTheory.EmbInj.mem_OL_iff LL x

theorem isOpen_integers {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) :
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1)) :=
  (GlobalTheory.LitGood.litGoodO l LL).2.2.2.2

theorem elem : ReciprocityTheory.ChartRestriction.T2.Elem where
  padicInt := padicInt_coeff
  mulSub := @fun _ _ _ _ _ _ _ _ _ _ _ hM hO _ ha => mulSub_open hM hO ha
  contQuot := fun h T hT => contAction_quotient h T hT
  swapCob := fun D x t c hc hcz => pr_eq_zero_of_coboundary D x t c hc hcz
  shapeEquiv := fun Hc F Hc' F' d e h => quotShape_of_equiv Hc F Hc' F' d e h
  memOL := fun LL x => mem_integers_iff_norm_le_one LL x
  openOL := fun LL => isOpen_integers LL

end GlobalTheory.LocElem
