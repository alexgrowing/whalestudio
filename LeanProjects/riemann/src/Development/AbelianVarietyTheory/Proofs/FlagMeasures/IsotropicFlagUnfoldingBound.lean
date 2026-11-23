import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsSatFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagsConjugateOfSameAdaptedModelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolProdLeTsumSlices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagClassMeasureBoundLatticeStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagUnfold

theorem tsum_pi_prod_le {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ENNReal) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ t ∈ s, ∏ i, f i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, f i (t i) := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _

abbrev latRel (E : Type) [Field E] [NumberField E] (j : ℕ) :
    {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} → Prop :=
  fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1

theorem latRel_equiv (E : Type) [Field E] [NumberField E] (j : ℕ) : Equivalence (latRel E j) := by
  refine ⟨fun Λ => ⟨1, fun y => by simp⟩, ?_, ?_⟩
  · rintro Λ Λ' ⟨γ, h⟩
    refine ⟨γ⁻¹, fun y => ?_⟩
    rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · rintro Λ Λ' Λ'' ⟨γ, h⟩ ⟨δ, h'⟩
    refine ⟨δ * γ, fun y => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h', h]

theorem countable_lattices (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Countable {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} := by
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have h : ∀ Λ : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ},
      ∃ s : Finset (Fin j → E), Submodule.span (𝓞 E) (s : Set (Fin j → E)) = Λ.1 := fun Λ => Λ.2.fg
  choose s hs using h
  refine Function.Injective.countable (f := s) fun a b hab => Subtype.ext ?_
  rw [← hs a, ← hs b, hab]

theorem exists_kSub (I : AutInst) : ∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset :=
  ⟨(Formalism.UG.stabGL I.Lf).comap (Subgroup.subtype _), rfl⟩

def dcRel {G₁ G₂ : Type} [Group G₁] [Group G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (x y : G₂) : Prop :=
  ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * x = y * k

theorem dcRel_equiv {G₁ G₂ : Type} [Group G₁] [Group G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) :
    Equivalence (dcRel Γ K) := by
  refine ⟨fun x => ⟨1, Γ.one_mem, 1, K.one_mem, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨γ, hγ, k, hk, h⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
    have : y = γ.2 * x * k⁻¹ := by rw [h]; group
    rw [this, Prod.snd_inv]; group
  · rintro x y z ⟨γ, hγ, k, hk, h⟩ ⟨δ, hδ, l, hl, h'⟩
    refine ⟨δ * γ, Γ.mul_mem hδ hγ, l * k, K.mul_mem hl hk, ?_⟩
    rw [Prod.snd_mul, mul_assoc, h, ← mul_assoc, h', mul_assoc]

theorem countable_dc {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [SecondCountableTopology G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (hK : IsOpen (K : Set G₂)) :
    Countable (Quot (dcRel Γ K)) := by
  have : DiscreteTopology (G₂ ⧸ K) := QuotientGroup.discreteTopology hK
  have : Countable (G₂ ⧸ K) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine Function.Surjective.countable (f := fun c : G₂ ⧸ K => Quot.mk (dcRel Γ K) c.out) ?_
  rintro ⟨x⟩
  refine ⟨(x : G₂ ⧸ K), Quot.sound ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  exact ⟨1, Γ.one_mem, k, k.2, by rw [hk]; simp⟩

theorem rel_out {α : Type} {r : α → α → Prop} (hr : Equivalence r) (x : α) : r x (Quot.out (Quot.mk r x)) :=
  hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk r x)).symm)

theorem sum_covol_le {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [T2Space G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₁.IsMulLeftInvariant]
    [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (hc : (Γ : Set (G₁ × G₂)).Countable)
    (hfin : ∀ C, IsCompact C → ((Γ : Set (G₁ × G₂)) ∩ C).Finite) (hinj : ∀ γ ∈ Γ, γ.1 = 1 → γ = 1)
    (hKc : IsCompact (K : Set G₂)) (hKo : IsOpen (K : Set G₂)) :
    μ₂ K * ∑' d : Quot (dcRel Γ K),
      covol {g | ∃ γ ∈ Γ, γ.1 = g ∧ (Quot.out d)⁻¹ * γ.2 * Quot.out d ∈ K} μ₁ Set.univ ≤
      covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) Set.univ := by
  have := countable_dc Γ K hKo
  have hF : ∀ x : G₂, ∃ F : Set G₁, MeasurableSet F ∧
      (∀ y, ∃ g ∈ {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}, g * y ∈ F) ∧
      ∀ g ∈ {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}, ∀ y ∈ F, g * y ∈ F → g = 1 := by
    intro x
    let Δ : Subgroup G₁ :=
      { carrier := {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}
        one_mem' := ⟨1, Γ.one_mem, rfl, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨γ, h1, rfl, h2⟩ ⟨δ, h3, rfl, h4⟩
          refine ⟨γ * δ, Γ.mul_mem h1 h3, rfl, ?_⟩
          convert K.mul_mem h2 h4 using 1
          rw [Prod.snd_mul]; group
        inv_mem' := by
          rintro _ ⟨γ, h1, rfl, h2⟩
          refine ⟨γ⁻¹, Γ.inv_mem h1, rfl, ?_⟩
          convert K.inv_mem h2 using 1
          rw [Prod.snd_inv]; group }
    have : Countable Δ := by
      refine Set.Countable.to_subtype (s := (Δ : Set G₁)) ((hc.image Prod.fst).mono ?_)
      rintro _ ⟨γ, h1, rfl, -⟩
      exact ⟨γ, h1, rfl⟩
    refine GlobalTheory.FundExists.exists_strict_domain Δ fun C hC => ?_
    refine ((hfin _ (hC.prod (hKc.image (f := fun k => x * k * x⁻¹) (by fun_prop)))).image Prod.fst).subset ?_
    rintro _ ⟨hC', γ, h1, rfl, h2⟩
    exact ⟨γ, ⟨h1, hC', _, h2, by group⟩, rfl⟩
  choose F hFm hFc hFi using hF
  let X : Quot (dcRel Γ K) → Set (G₁ × G₂) := fun d =>
    F (Quot.out d) ×ˢ ((fun z => (Quot.out d)⁻¹ * z) ⁻¹' (K : Set G₂))
  have hXm : ∀ d, MeasurableSet (X d) := fun d =>
    (hFm _).prod (measurable_const_mul _ hKo.measurableSet)
  have hkey : ∀ γ ∈ Γ, ∀ d d' y, y ∈ X d → γ * y ∈ X d' → d = d' ∧ γ = 1 := by
    intro γ hγ d d' y hy hy'
    have h1 : (Quot.out d)⁻¹ * y.2 ∈ K := hy.2
    have h2 : (Quot.out d')⁻¹ * (γ.2 * y.2) ∈ K := hy'.2
    have h3 := K.mul_mem h2 (K.inv_mem h1)
    have hd : d = d' := by
      rw [← Quot.out_eq d, ← Quot.out_eq d']
      exact Quot.sound ⟨γ, hγ, _, h3, by group⟩
    subst hd
    refine ⟨rfl, hinj γ hγ (hFi _ γ.1 ⟨γ, hγ, rfl, ?_⟩ y.1 hy.1 hy'.1)⟩
    convert h3 using 1
    group
  rw [GlobalTheory.covol_eq_measure_inter_fund (G₁ × G₂) Γ (μ₁.prod μ₂) (⋃ d, X d) Set.univ hc
    (fun γ _ => map_mul_left_eq_self _ γ) (MeasurableSet.iUnion hXm) ?_ ?_ MeasurableSet.univ (by simp),
    Set.univ_inter, measure_iUnion ?_ hXm, ← ENNReal.tsum_mul_left]
  · refine ENNReal.tsum_le_tsum fun d => ?_
    rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
    gcongr
    exact iInf_le_of_le (F _) (iInf_le_of_le (hFm _) (iInf_le_of_le (fun y _ => hFc _ y) le_rfl))
  · intro d d' hd
    refine Set.disjoint_left.2 fun y hy hy' => hd (hkey 1 Γ.one_mem d d' y hy (by rwa [one_mul])).1
  · intro y
    obtain ⟨γ, hγ, k, hk, h⟩ := rel_out (dcRel_equiv Γ K) y.2
    obtain ⟨_, ⟨δ, hδ, rfl, hδK⟩, h'⟩ := hFc (Quot.out (Quot.mk (dcRel Γ K) y.2)) (γ.1 * y.1)
    refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨Quot.mk _ y.2, ?_, ?_⟩⟩
    · simpa [mul_assoc] using h'
    · show _ * (δ.2 * γ.2 * y.2) ∈ K
      rw [mul_assoc δ.2, h]
      convert K.mul_mem hδK hk using 1
      group
  · intro γ hγ hne
    have : (fun y => γ * y) '' (⋃ d, X d) ∩ (⋃ d, X d) = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hγy⟩
      obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hy
      obtain ⟨d', hd'⟩ := Set.mem_iUnion.1 hγy
      exact hne (hkey γ hγ d d' y hd hd').2
    rw [this, measure_empty]

theorem eq_one_of_fst (I : AutInst) (x : I.GA) (hx : x ∈ I.GFset) (h : x.1 = 1) : x = 1 := by
  obtain ⟨γ, -, h1, h2⟩ := hx
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hP := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h3 := h1 v
  rw [h] at h3
  have h4 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
    have h5 : (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v = 1 := h3.symm
    have h6 := congrArg (fun M => I.P v * M * (I.P v)⁻¹) h5
    simp only [← Matrix.mul_assoc] at h6
    rwa [Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hP, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ hP] at h6
  have h7 : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1 := by
    refine Matrix.map_injective (I.φ v).injective ?_
    show _ = (1 : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4
  rw [h7, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact Prod.ext h (Subtype.ext (Units.ext h2))

theorem sum_latGroup_le (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset)
    (K : Subgroup I.Gf) (hK : (K : Set I.Gf) = I.Kset) (c : InfinitePlace I.F → ℝ)
    (μ : Measure I.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] :
    ∑' d : Quot (dcRel Γ K), ENNReal.ofReal (∏ v, c v) *
      covol (latGroup I (Quot.out d)) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) Set.univ ≤ gaugeVol I c μ := by
  obtain ⟨hc, ho, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have := countable_dc Γ K (hK ▸ ho)
  have : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have h0 : μ I.Kset ≠ 0 := (ho.measure_pos μ ⟨1, hK ▸ K.one_mem⟩).ne'
  have ht : μ I.Kset ≠ ⊤ := hc.measure_lt_top.ne
  have key := sum_covol_le (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) μ Γ K
    (hΓ ▸ (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).2.1)
    (hΓ ▸ (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).2.2)
    (fun γ hγ => eq_one_of_fst I γ (hΓ ▸ hγ)) (hK ▸ hc) (hK ▸ ho)
  have e1 : ∀ x : I.Gf, {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K} = latGroup I x := fun x => by
    unfold latGroup
    rw [← hΓ, ← hK]; rfl
  simp only [e1] at key
  rw [hΓ, hK] at key
  rw [ENNReal.tsum_mul_left, gaugeVol, mul_div_assoc]
  gcongr
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht), mul_comm]
  exact key

theorem unfoldBound : UnfoldBound := by
  intro I I₀ p q a j _ hj hq hp hsame hsig hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀ B hB hBs
  obtain ⟨e, he⟩ := hsame
  obtain ⟨Γ, hΓ⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).1
  obtain ⟨Γ₀, hΓ₀⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I₀).1
  obtain ⟨K, hK⟩ := exists_kSub I
  obtain ⟨K₀, hK₀⟩ := exists_kSub I₀
  obtain ⟨hcK, hoK, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I₀
  have := countable_dc Γ₀ K₀ (hK₀ ▸ (GlobalTheory.adelicStab_isCompact_isOpen I₀).2.1)
  have := fun i => countable_lattices I.E (j i)
  have h0 : μf I.Kset ≠ 0 := (hoK.measure_pos μf ⟨1, hK ▸ K.one_mem⟩).ne'
  have ht : μf I.Kset ≠ ⊤ := hcK.measure_lt_top.ne
  let P : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) → Prop := fun t =>
    ∃ xf S T T' T₀, IsAdapted I I₀ e xf j S (fun i => (Quot.out (t.1 i)).1) (Quot.out t.2) T T' T₀
  have hP : ∀ t : {t // P t}, ∃ xf S T T' T₀,
    IsAdapted I I₀ e xf j S (fun i => (Quot.out (t.1.1 i)).1) (Quot.out t.1.2) T T' T₀ := fun t => t.2
  choose x S T T' T₀ had using hP
  have key := GlobalTheory.FlagMeas.covol_prod_le_tsum_slices I.Ginf I.Gf (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) μf Γ K (typeSet I j B)
    {t // P t} x (fun t => flagGroup I (x t) (S t)) (fun t => {g | sizesAt I (x t) (S t) g ∈ B})
    (hK ▸ hoK.measurableSet)
    (fun t g hg => by
      obtain ⟨γ, h1, h2, h3⟩ := hg.1
      exact ⟨γ, by rwa [← SetLike.mem_coe, hΓ], h2, by rwa [← SetLike.mem_coe, hK]⟩)
    (fun y hy => by
      obtain ⟨R, hR, hRB⟩ := GlobalTheory.FlagSat.exists_isSatFlag I a j B y hy
      obtain ⟨Λ, x₀, U, U', U₀, hU⟩ := GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag I I₀ e p q a j he hsig hp hq hsig₀ y.2 R hR
      let t : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) :=
        (fun i => Quot.mk _ ⟨Λ i, hU.2.2.1 i⟩, Quot.mk _ x₀)
      obtain ⟨V, V', V₀, hV⟩ := GlobalTheory.T.exists_adapted_basis_change_models I I₀ e y.2 a j R Λ x₀ U U' U₀ hj hU
        (fun i => (Quot.out (t.1 i)).1) (Quot.out t.2)
        (fun i => rel_out (latRel_equiv I.E (j i)) ⟨Λ i, hU.2.2.1 i⟩)
        (by
          obtain ⟨γ, h1, k, h2, h3⟩ := rel_out (dcRel_equiv Γ₀ K₀) x₀
          exact ⟨γ, hΓ₀ ▸ h1, k, hK₀ ▸ h2, h3⟩)
      let t' : {t // P t} := ⟨t, y.2, R, V, V', V₀, hV⟩
      obtain ⟨γ, h1, k, h2, h3, h4⟩ := GlobalTheory.T.flags_conjugate_of_same_adapted_models I I₀ e y.2 a j R _ _ V V' V₀ hj hV (x t') (S t') (T t') (T' t')
        (T₀ t') (had t')
      refine ⟨t', γ, by rwa [← SetLike.mem_coe, hΓ], k, by rwa [← SetLike.mem_coe, hK], h3, ?_⟩
      show sizesAt I (x t') (S t') (γ.1 * y.1) ∈ B
      rwa [h4])
    (hK ▸ ht)
  rw [hΓ, hK] at key
  have loc := fun t : {t // P t} => GlobalTheory.T.flagClass_measure_bound_lattice_stabiliser I I₀ e (x t) a j (S t) _ _ (T t) (T' t) (T₀ t) hj (had t)
    p q hsig c c₀ hc hc₀ B hB hBs
  set C := ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) with hC
  set Z := ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) with hZ
  let f : ∀ i, Quot (latRel I.E (j i)) → ENNReal := fun i d =>
    ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Quot.out d).1
  let g : Quot (dcRel Γ₀ K₀) → ENNReal := fun d => ENNReal.ofReal (∏ v, c₀ v) *
      covol (latGroup I₀ (Quot.out d)) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ
  have hg : ∑' d, g d ≤ gaugeVol I₀ c₀ μ₀ := sum_latGroup_le I₀ Γ₀ hΓ₀ K₀ hK₀ c₀ μ₀
  have hf : ∑' t : ∀ i, Quot (latRel I.E (j i)), ∏ i, f i (t i) ≤
      ∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i) := by
    refine (tsum_pi_prod_le f).trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
    rw [ENNReal.tsum_mul_left]; rfl
  have hsum : ∑' t : {t // P t}, C * (∏ i, f i (t.1.1 i)) * g t.1.2 * Z ≤
      C * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i)) * gaugeVol I₀ c₀ μ₀ * Z := by
    refine (ENNReal.tsum_comp_le_tsum_of_injective (f := Subtype.val) Subtype.val_injective
      (fun t : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) =>
        C * (∏ i, f i (t.1 i)) * g t.2 * Z)).trans ?_
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    gcongr
  refine le_trans ?_ hsum
  refine le_trans ?_ (ENNReal.tsum_le_tsum loc)
  rw [ENNReal.tsum_mul_left, mul_div_assoc]
  gcongr
  rw [ENNReal.div_le_iff h0 ht, mul_comm]
  exact key

end GlobalTheory.FlagUnfold
