import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrand
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime
import ReciprocityTheory.GroupCohomology.FiniteLevel

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

section Cyclic

variable {R : Type} [CommRing R] {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C] [DiscreteTopology C]

theorem cyc_odd (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃ₗ[R] (LinearMap.ker M.rho.norm ⧸
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype)) := by
  have : IsCyclic C := ⟨g, hg⟩
  let : CommGroup C := IsCyclic.commGroup
  exact nonempty_cyclic_odd M g hg i hi

theorem cyc_even (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (h0 : i ≠ 0)
    (hi : Even i) :
    Nonempty (M.H i ≃ₗ[R] (M.rho.invariants ⧸
      (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype)) := by
  have : IsCyclic C := ⟨g, hg⟩
  let : CommGroup C := IsCyclic.commGroup
  exact nonempty_cyclic_even M g hg i h0 hi

theorem norm_apply' (M : TRep R C) (u : M.V) : M.rho.norm u = ∑ c, M.rho c u := by
  simp [Representation.norm]

theorem exists_sub_eq_of_cyclic_of_h1_subsingleton (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (h1 : Subsingleton (M.H 1))
    (u : M.V) (hu : ∑ c, M.rho c u = 0) : ∃ w, M.rho g w - w = u := by
  obtain ⟨e⟩ := cyc_odd M g hg 1 (by decide)
  have hs := e.symm.injective.subsingleton
  rw [Submodule.Quotient.subsingleton_iff] at hs
  have hk : u ∈ LinearMap.ker M.rho.norm := by rw [LinearMap.mem_ker, norm_apply', hu]
  have hm : (⟨u, hk⟩ : LinearMap.ker M.rho.norm) ∈
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype := by
    rw [hs]; exact Submodule.mem_top
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, hw⟩

theorem cyc_subsingleton (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hN : ∀ u, (∀ c, M.rho c u = u) → ∃ w, ∑ c, M.rho c w = u)
    (hD : ∀ u, ∑ c, M.rho c u = 0 → ∃ w, M.rho g w - w = u) (i : ℕ) (hi : 0 < i) :
    Subsingleton (M.H i) := by
  rcases Nat.even_or_odd i with h | h
  · obtain ⟨e⟩ := cyc_even M g hg i hi.ne' h
    have : Subsingleton (M.rho.invariants ⧸
        (LinearMap.range M.rho.norm).comap M.rho.invariants.subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      rintro ⟨u, hu⟩ -
      obtain ⟨w, hw⟩ := hN u hu
      exact ⟨w, by rw [norm_apply', hw]; rfl⟩
    exact e.injective.subsingleton
  · obtain ⟨e⟩ := cyc_odd M g hg i h
    have : Subsingleton (LinearMap.ker M.rho.norm ⧸
        (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      rintro ⟨u, hu⟩ -
      obtain ⟨w, hw⟩ := hD u (by rw [← norm_apply']; exact hu)
      exact ⟨w, hw⟩
    exact e.injective.subsingleton

end Cyclic

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K}

theorem exists_frob_sub_eq_of_sum_eq_zero_layerU (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    [Fintype (GalLK p K (Kn p K n))] (u : (layerU p K (Kn p K n)).V)
    (hu : ∑ g, (layerU p K (Kn p K n)).rho g u = 0) :
    ∃ w, (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n)) w - w = u := by
  have hL := finiteDimensional_Kn p K hK hn
  have hKL : K ≤ Kn p K n := le_sup_left
  have := discreteTopology_GalLK (K := K) hL
  have hg := mem_zpowers_frobLK_Kn hK hn
  have h1 : Subsingleton ((layer p K (Kn p K n)).H 1) :=
    quotient_multiplicative_h1_subsingleton p K _ _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
  have hI : ∀ g x, (layerUIncl p K (Kn p K n)).u ((layerU p K (Kn p K n)).rho g x) =
      (layer p K (Kn p K n)).rho g ((layerUIncl p K (Kn p K n)).u x) :=
    (layerUIncl p K (Kn p K n)).equiv
  obtain ⟨w, hw⟩ := exists_sub_eq_of_cyclic_of_h1_subsingleton (layer p K (Kn p K n)) _ hg h1 ((layerUIncl p K (Kn p K n)).u u) (by
    simp only [← hI]
    rw [← map_sum, hu, map_zero])
  obtain ⟨π, hπ⟩ := vOn_surjective p K hK 1
  have hπL : π.1 ∈ multOf p (Kn p K n) := hKL π.2
  let π' : (layer p K (Kn p K n)).V := toLayer p ⟨π.1, hπL⟩
  have hπ' : vLayerMap p K (Kn p K n) π' = 1 := by
    rw [vLayerMap_of_mem p hL hKL π' π.2, eLK_Kn p hK hn]
    show ((1 : ℕ) : ℤ) * vOn p K π = 1
    rw [hπ]; simp
  have hfix : ∀ g, (layer p K (Kn p K n)).rho g π' = π' := (layer_invariant_iff π').2 π.2
  have he : 0 < eK p (Kn p K n) := eK_pos p _ hL
  have h0 : vLayerMap p K (Kn p K n) (w - vLayerMap p K (Kn p K n) w • π') = 0 := by
    rw [map_sub, map_zsmul, hπ']; simp
  obtain ⟨w', hw'⟩ := (vLayerMap_eq_zero_iff p he hKL _).1 h0
  refine ⟨w', layerUIncl_injective p ?_⟩
  rw [map_sub, hI, hw', map_sub, map_zsmul, hfix, ← hw]
  abel

theorem layerU_Kn_norm_surjective (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n)
    [Fintype (GalLK p K (Kn p K n))] (u : (layerU p K (Kn p K n)).V)
    (hu : ∀ g, (layerU p K (Kn p K n)).rho g u = u) :
    ∃ w, ∑ g, (layerU p K (Kn p K n)).rho g w = u := by
  have hL := finiteDimensional_Kn p K hK hn
  have hKL : K ≤ Kn p K n := le_sup_left
  have hg := mem_zpowers_frobLK_Kn hK hn
  obtain ⟨hfin, h1⟩ := herbrand_layerU hK hL hKL _ hg
  have : Subsingleton (Herbrand.H1 (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [Herbrand.mk_eq_mk_iff]
    have hxy : ∑ g, (layerU p K (Kn p K n)).rho g ((x : (layerU p K (Kn p K n)).V) - y) = 0 := by
      rw [← Herbrand.nHom_apply, map_sub]
      rw [show Herbrand.nHom (layerU p K (Kn p K n)).rho x = 0 from x.2,
        show Herbrand.nHom (layerU p K (Kn p K n)).rho y = 0 from y.2, sub_zero]
    obtain ⟨w, hw⟩ := exists_frob_sub_eq_of_sum_eq_zero_layerU hK hn _ hxy
    exact ⟨w, hw⟩
  rw [Herbrand.h_eq_card_H0hat] at h1
  have h2 : Nat.card (Herbrand.TateZerothCohomology (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))) = 1 := by
    exact_mod_cast h1
  have := hfin.1
  have h3 := (Nat.card_eq_one_iff_unique.1 h2).1
  have hk : u ∈ (Herbrand.dHom (layerU p K (Kn p K n)).rho (frobLK p K (Kn p K n))).ker :=
    (Herbrand.mem_ker_dHom_iff _ _ hg u).2 hu
  have h4 := (Herbrand.mk_eq_zero_iff (N := Herbrand.nHom (layerU p K (Kn p K n)).rho) ⟨u, hk⟩).1
    (Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := h4
  exact ⟨w, by rw [← Herbrand.nHom_apply]; exact hw⟩

theorem layerU_Kn_H_subsingleton (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((layerU p K (Kn p K n)).H i) := by
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := finite_GalLK (K := K) hL
  let := Fintype.ofFinite (GalLK p K (Kn p K n))
  exact cyc_subsingleton _ _ (mem_zpowers_frobLK_Kn hK hn) (layerU_Kn_norm_surjective hK hn)
    (exists_frob_sub_eq_of_sum_eq_zero_layerU hK hn) i hi

theorem layerU_Kur_level (hK : FiniteDimensional ℚ_[p] K) (N : Subgroup (GalLK p K (MaximalUnramifiedExtension p K))) [N.Normal]
    (hN : IsOpen (N : Set (GalLK p K (MaximalUnramifiedExtension p K)))) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).H i) := by
  obtain ⟨n, hn, hU⟩ := exists_Kn_of_isOpen hK (N.comap (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))))
    (hN.preimage continuous_quot_mk) (fun σ hσ => by
      show (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ N
      rw [(QuotientGroup.eq_one_iff σ).2 hσ]
      exact N.one_mem)
  have hU' : ∀ σ : GK p K, (QuotientGroup.mk σ : GalLK p K (MaximalUnramifiedExtension p K)) ∈ N ↔ σ ∈ subG p K (Kn p K n) :=
    fun σ => by rw [← hU]; rfl
  have hL := finiteDimensional_Kn p K hK hn
  have := discreteTopology_GalLK (K := K) hL
  have := QuotientGroup.discreteTopology hN
  have : DiscreteTopology (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).V :=
    (InflationRestrictionInvariants.invariants_isInvRep (layerU p K (MaximalUnramifiedExtension p K)) N).2.1.discreteTopology
  let θ : GalLK p K (Kn p K n) →* GalLK p K (MaximalUnramifiedExtension p K) ⧸ N :=
    QuotientGroup.lift (subG p K (Kn p K n))
      ((QuotientGroup.mk' N).comp (QuotientGroup.mk' (subG p K (MaximalUnramifiedExtension p K))))
      (fun σ hσ => (QuotientGroup.eq_one_iff _).2 ((hU' σ).2 hσ))
  have hθ : Bijective θ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro g hg
      induction g using QuotientGroup.induction_on with
      | H σ => exact (QuotientGroup.eq_one_iff σ).2 ((hU' σ).1 ((QuotientGroup.eq_one_iff _).1 hg))
    · intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        induction g using QuotientGroup.induction_on with
        | H σ => exact ⟨QuotientGroup.mk σ, rfl⟩
  let u : (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N).V →+ (layerU p K (Kn p K n)).V :=
    { toFun := fun x => ⟨x.1.1, fun σ => congrArg Subtype.val (x.2 ⟨QuotientGroup.mk σ.1, (hU' σ.1).2 σ.2⟩)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hu : Bijective u := by
    constructor
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (layerU p K (Kn p K n)).V => z.1) hxy))
    · intro z
      refine ⟨⟨⟨z.1, fun σ => z.2 ⟨σ.1, subG_anti (Kn_le_Kur hn) σ.2⟩⟩, fun g => ?_⟩, rfl⟩
      obtain ⟨g, hg⟩ := g
      induction g using QuotientGroup.induction_on with
      | H σ => exact Subtype.ext (z.2 ⟨σ, (hU' σ).1 hg⟩)
  let R : Pair (InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N) (layerU p K (Kn p K n)) :=
    { φ := θ
      u := mkLin (A := InflationRestrictionInvariants.invQ (layerU p K (MaximalUnramifiedExtension p K)) N) (B := layerU p K (Kn p K n)) u
      φ_cont := continuous_of_discreteTopology
      u_cont := continuous_of_discreteTopology
      equiv := fun g m => by
        induction g using QuotientGroup.induction_on with
        | H σ => rfl }
  have hb := pair_H_bijective R ⟨continuous_of_discreteTopology, fun _ _ => isOpen_discrete _, hθ⟩
    ⟨continuous_of_discreteTopology, fun _ _ => isOpen_discrete _, hu⟩ i
  have := layerU_Kn_H_subsingleton hK hn i hi
  exact hb.1.subsingleton

theorem layerU_Kur_H_subsingleton (hK : FiniteDimensional ℚ_[p] K) (i : ℕ) (hi : 0 < i) :
    Subsingleton ((layerU p K (MaximalUnramifiedExtension p K)).H i) := by
  have h0 : ∀ x : (layerU p K (MaximalUnramifiedExtension p K)).H i, x = 0 := fun x => by
    obtain ⟨⟨N, hNn, hNo, h⟩, -⟩ := finiteLevel_holds ℤ (GalLK p K (MaximalUnramifiedExtension p K)) (layerU p K (MaximalUnramifiedExtension p K)) i x
    obtain ⟨y, rfl⟩ := h _ _ (InflationRestrictionInvariants.invariants_isInvRep (layerU p K (MaximalUnramifiedExtension p K)) N)
    have := layerU_Kur_level hK N hNo i hi
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
