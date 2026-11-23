import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosedStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvMeasure

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fundamentalDomain_subset [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G}
    (hK : IsClosed K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) :
    ∃ S ⊆ K, IsFundamentalDomain Γ S μ := by
  classical
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  obtain ⟨c, hc⟩ := exists_injective_nat Γ
  let S : Set G := K ∩ ⋃ g : Γ, ((fun y => g • y) ⁻¹' D ∩ ⋂ h : Γ, ⋂ _ : c h < c g, ((fun y => (h⁻¹ * g) • y) ⁻¹' K)ᶜ)
  have hS : ∀ y, y ∈ S ↔ y ∈ K ∧ ∃ g : Γ, g • y ∈ D ∧ ∀ h : Γ, c h < c g → (h⁻¹ * g) • y ∉ K := fun y => by
    simp only [S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  refine ⟨S, Set.inter_subset_left, IsFundamentalDomain.mk' (MeasurableSet.nullMeasurableSet ?_) fun x => ?_⟩
  · exact hK.measurableSet.inter <| MeasurableSet.iUnion fun g => (measurable_const_smul g hD).inter <|
      MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ => (measurable_const_smul _ hK.measurableSet).compl
  · obtain ⟨d, hd, hdu⟩ := hu x
    have hex : ∃ n, ∃ g : Γ, c g = n ∧ (g⁻¹ * d) • x ∈ K := by
      obtain ⟨γ, hγ, h⟩ := hcov x
      refine ⟨_, d * (⟨γ, hγ⟩ : Γ)⁻¹, rfl, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
      exact h
    obtain ⟨g, hg, hgK⟩ := Nat.find_spec hex
    refine ⟨g⁻¹ * d, (hS _).2 ⟨hgK, g, ?_, fun h hh hK' => ?_⟩, fun k hk => ?_⟩
    · rw [smul_smul, mul_inv_cancel_left]; exact hd
    · refine Nat.find_min hex (hg ▸ hh) ⟨h, rfl, ?_⟩
      rwa [smul_smul, mul_assoc, mul_inv_cancel_left] at hK'
    · obtain ⟨hkK, g', h1, h2⟩ := (hS _).1 hk
      rw [smul_smul] at h1
      have e : g' * k = d := hdu _ h1
      have ek : k = g'⁻¹ * d := by rw [← e, inv_mul_cancel_left]
      have hle : Nat.find hex ≤ c g' := Nat.find_min' hex ⟨g', rfl, ek ▸ hkK⟩
      rcases hle.eq_or_lt with h | h
      · rw [ek, hc (hg.trans h)]
      · refine (h2 g (hg ▸ h) ?_).elim
        rw [smul_smul, mul_assoc, e]
        exact hgK

open Pointwise in

theorem measure_ne_top_of_cocompact (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F ≠ ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hg⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  refine ne_of_lt ?_
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

end General

theorem exists_sub_mem_of_isOpen (F : Type) [Field F] [NumberField F] (W : AddSubgroup (AF F))
    (hW : IsOpen (W : Set (AF F))) (a : AF F) : ∃ x : F, a - algebraMap F (AF F) x ∈ W := by
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let H : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range ⊔ W
  have hH : IsOpen (H : Set (AF F)) := AddSubgroup.isOpen_mono le_sup_right hW
  have hd : DiscreteTopology (AF F ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hf : Finite (AF F ⧸ H) := by
    have h1 : (QuotientAddGroup.mk '' K : Set (AF F ⧸ H)).Finite :=
      (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
    refine Set.finite_univ_iff.1 (h1.subset fun q _ => ?_)
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, h⟩ := hx b
    refine ⟨_, h, QuotientAddGroup.eq.2 ?_⟩
    have : -(b - algebraMap F (AF F) x) + b = algebraMap F (AF F) x := by ring
    rw [this]
    exact AddSubgroup.mem_sup_left ⟨x, rfl⟩
  have hn : (H.index : F) ≠ 0 := Nat.cast_ne_zero.2 H.index_ne_zero_of_finite
  have hm := H.nsmul_index_mem ((H.index : F)⁻¹ • a)
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hn, one_smul] at hm
  obtain ⟨_, ⟨x, rfl⟩, w, hw, e⟩ := AddSubgroup.mem_sup.1 hm
  refine ⟨x, ?_⟩
  rw [← e]
  simpa using hw

theorem map_proj {R A n : Type} [CommRing R] [CommRing A] [DecidableEq n] (f : R →+* A) (ε : R) (M : Matrix n n R) :
    (f ε = 0 → (1 + ε • (M - 1)).map f = 1) ∧ (f ε = 1 → (1 + ε • (M - 1)).map f = M.map f) := by
  constructor <;> intro h <;> ext i j <;> by_cases hij : i = j <;> simp [h, Matrix.one_apply, hij]

theorem continuous_proj {X R n : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DecidableEq n] (ε : R) {M : X → Matrix n n R} (h : Continuous M) : Continuous fun x => 1 + ε • (M x - 1) :=
  continuous_const.add ((h.sub continuous_const).const_smul ε)

theorem proj_smul {R n : Type} [CommRing R] [DecidableEq n] (ε a : R) {M M' N : Matrix n n R}
    (h : M' = 1 + ε • (M - 1)) (ha : M - 1 = a • N) : M' - 1 = (ε * a) • N := by
  rw [h, ha, add_sub_cancel_left, smul_smul]

variable {D : D7}

theorem exists_finite_projection_mat (V : HSp D) : ∃ (p : GA D V →* GA D V) (ε : AE D), (∀ g, infHom V (p g) = 1) ∧
    (∀ g, finHom V (p g) = finHom V g) ∧ ∀ g, (matHom V (p g)).1 = 1 + ε • ((matHom V g).1 - 1) := by
  choose q h1 h2 using fun g : GA D V =>
    GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  obtain ⟨ε, e1, e2⟩ := GlobalTheory.UnitarySplit.parts_surj D 0 1
  refine ⟨MonoidHom.mk' q fun a b => GlobalTheory.UnitarySplit.ga_ext V
    (by rw [map_mul, h1, h1, h1, mul_one]) (by rw [h2, map_mul, map_mul, h2, h2]), ε, h1, h2, fun g => ?_⟩
  refine GlobalTheory.UnitarySplit.mat_ext (infPart D) (finPart D) (GlobalTheory.UnitarySplit.parts_inj D) ?_ ?_
  · exact (congrArg Units.val (h1 g)).trans ((map_proj (infPart D) ε _).1 e1).symm
  · exact (congrArg Units.val (h2 g)).trans ((map_proj (finPart D) ε _).2 e2).symm

theorem exists_finite_projection (V : HSp D) : ∃ p : GA D V →* GA D V, Continuous p ∧ (∀ g, p g ∈ GfC V) ∧
    (∀ g, g * (p g)⁻¹ ∈ GinfC V) ∧ ∀ ξ, ∀ g ∈ ZI V ξ, p g ∈ ZI V ξ := by
  obtain ⟨p, ε, h1, h2, hm⟩ := exists_finite_projection_mat V
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hc : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  have hc' : Continuous fun g : GA D V => (matHom V (p g)).1 :=
    (continuous_proj (R := AE D) ε hc).congr fun g => (hm g).symm
  refine ⟨p, ?_, h1, fun g => ?_, fun ξ g hg => ?_⟩
  · have h3 : Continuous fun g : GA D V => matHom V (p g) := by
      refine Units.continuous_iff.2 ⟨hc', (hc'.comp (continuous_inv (G := GA D V))).congr fun g => ?_⟩
      rw [Function.comp_apply, map_inv, map_inv]
    exact continuous_induced_rng.2 h3
  · change finHom V (g * (p g)⁻¹) = 1
    rw [map_mul, map_inv, h2 g, mul_inv_cancel]
  · have : ZI V ξ ≤ (ZI V ξ).comap p := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨a, ha⟩
      exact Subgroup.subset_closure ⟨ε * a, proj_smul ε a (hm g) ha⟩
    exact this hg

theorem transvection_measure : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure ∧ IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ ∧ IsCompact (closure 𝓕)) ∧ (∀ (μ : Measure (ZI V ξ)) (𝓕 : Set (ZI V ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ V).subgroupOf (ZI V ξ)) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤) ∧ ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ z ∈ ZI V ξ, ∃ γ ∈ ZI V ξ, γ ∈ GQ V ∧ ∃ u ∈ ZI V ξ, u ∈ GinfC V ∧ ∃ k ∈ ZI V ξ, k ∈ GfC V ∧ k ∈ U ∧ z = γ * u * k := by
  intro D θ V hθ ξ hξ
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have i4 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  obtain ⟨-, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have : LocallyCompactSpace (Multiplicative (AF D.host.F)) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : LocallyCompactSpace (ZI V ξ) := e.toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI V ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hd : DiscreteTopology ((GQ V).subgroupOf (ZI V ξ)) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F
    refine discreteTopology_of_isOpen_singleton_one ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : (GQ V).subgroupOf (ZI V ξ) => Multiplicative.toAdd (e.symm x)) 1 :=
      (continuous_toAdd.comp (e.symm.continuous.comp continuous_subtype_val)).continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds (by simpa using hU)) ?_
    rintro ⟨z, hz⟩ hy
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hxa⟩ := (he a).1 hz
    have hy' : Multiplicative.toAdd a ∈ U := by simpa using hy
    have h0 : x = 0 := hx x (hxa ▸ hy')
    have : a = 1 := by
      rw [h0, map_zero] at hxa
      exact Multiplicative.toAdd.injective hxa.symm
    subst this
    exact Subtype.ext (map_one e)
  have := GlobalTheory.countable_of_discrete_subgroup ((GQ V).subgroupOf (ZI V ξ))
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  have hK' : IsCompact ((fun a => e (Multiplicative.ofAdd a)) '' K) :=
    hK.image (e.continuous.comp continuous_ofAdd)
  have hcov : ∀ z : ZI V ξ, ∃ γ ∈ (GQ V).subgroupOf (ZI V ξ), γ * z ∈ (fun a => e (Multiplicative.ofAdd a)) '' K := by
    intro z
    obtain ⟨a, rfl⟩ := e.surjective z
    obtain ⟨x, hx⟩ := hKx a.toAdd
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ (-x))), (he _).2 ⟨-x, rfl⟩, _, hx, ?_⟩
    beta_reduce
    rw [← map_mul, map_neg, sub_eq_neg_add]
    rfl
  refine ⟨?_, fun μ 𝓕 hμ h𝓕 => ⟨h𝓕.measure_ne_zero (NeZero.ne μ), measure_ne_top_of_cocompact _ hK' hcov μ h𝓕⟩,
    fun U hU z hz => ?_⟩
  · obtain ⟨S, hS, h⟩ := exists_fundamentalDomain_subset _ hK'.isClosed hcov Measure.haar
    exact ⟨Measure.haar, S, inferInstance, h, hK'.closure_of_subset hS⟩
  · obtain ⟨p, hp, h1, h2, h3⟩ := exists_finite_projection V
    let f : Multiplicative (AF D.host.F) →* GA D V := p.comp ((ZI V ξ).subtype.comp e.toMulEquiv.toMonoidHom)
    have hf : Continuous f := hp.comp (continuous_subtype_val.comp e.continuous)
    obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
    obtain ⟨x, hx⟩ := exists_sub_mem_of_isOpen D.host.F (Subgroup.toAddSubgroup' (U.comap f))
      (hU.preimage (hf.comp continuous_ofAdd)) a.toAdd
    set k : ZI V ξ := e (Multiplicative.ofAdd (a.toAdd - algebraMap _ _ x)) with hk
    have hkU : p k ∈ U := hx
    refine ⟨e (Multiplicative.ofAdd (algebraMap _ _ x)), SetLike.coe_mem _, (he _).2 ⟨x, rfl⟩,
      k * (p k)⁻¹, mul_mem k.2 (inv_mem (h3 ξ _ k.2)), h2 _, p k, h3 ξ _ k.2, h1 _, hkU, ?_⟩
    rw [mul_assoc, inv_mul_cancel_right, hk, ← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, add_sub_cancel,
      ofAdd_toAdd, ha]

end GlobalTheory.TransvMeasure
