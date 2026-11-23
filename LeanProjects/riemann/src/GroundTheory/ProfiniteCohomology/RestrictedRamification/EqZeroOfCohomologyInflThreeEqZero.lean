import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

theorem eq_zero_of_coprime_nsmul_of_pow_nsmul {M : Type*} [AddCommGroup M] {ℓ m j : ℕ}
    (hm : m.Coprime ℓ) {x : M} (h1 : m • x = 0) (h2 : ℓ ^ j • x = 0) : x = 0 := by
  have hd : addOrderOf x ∣ Nat.gcd m (ℓ ^ j) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [Nat.Coprime.gcd_eq_one (hm.pow_right j), Nat.dvd_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.1 hd

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem eq_zero_of_cohomologyInfl_three_eq_zero (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G)
    [N.Normal] (hN : IsClosed (N : Set G)) (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (ℓ : ℕ)
    (h2 : ∀ y : cohomology (Rep.res N.subtype A) 2, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (x : cohomology (A.quotientToInvariants N) 3) (hx : (cohomologyInfl A N 3).hom x = 0)
    (j : ℕ) (hj : ℓ ^ j • x = 0) : x = 0 := by
  have hX := coindShortComplex_shortExact A
  have hS := shortExact_map_res N hX
  have hQ := shortExact_map_quotientToInvariants_coindShortComplex A N h1
  have hδQ : IsIso (δ hQ (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hQ 1
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N 1)
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N (1 + 1))
  have hδX : IsIso (δ hX (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hX 1
    (isZero_cohomology_discreteCoind k G A 1) (isZero_cohomology_discreteCoind k G A (1 + 1))
  have hδS : IsIso (δ hS (0 + 1) (0 + 1 + 1) rfl) := isIso_δ_of_isZero hS 0
    (isZero_cohomology_res_discreteCoind (k := k) A N hN 0)
    (isZero_cohomology_res_discreteCoind (k := k) A N hN (0 + 1))
  have injQ : Function.Injective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injX : Function.Injective (δ hX (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injS : Function.Injective (δ hS (0 + 1) (0 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have surjQ : Function.Surjective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x', rfl⟩ := surjQ x
  have hsq := δ_comp_cohomologyInfl N hX hQ (1 + 1) (1 + 1 + 1) rfl
  have hx' : (cohomologyInfl (coindCokernel A) N (1 + 1)).hom x' = 0 := by
    have e : (δ hX (1 + 1) (1 + 1 + 1) rfl).hom ((cohomologyInfl (coindCokernel A) N (1 + 1)).hom x') =
        (cohomologyInfl A N 3).hom ((δ hQ (1 + 1) (1 + 1 + 1) rfl).hom x') :=
      (congrArg (fun φ => ModuleCat.Hom.hom φ x') hsq).symm
    exact injX (e.trans (hx.trans (map_zero _).symm))
  have hmem : x' ∈ LinearMap.ker (cohomologyInfl (coindCokernel A) N 2).hom := hx'
  rw [← (fiveTerm_exact (coindCokernel A) N hN).2.2.2] at hmem
  obtain ⟨w, rfl⟩ := hmem
  obtain ⟨m, hm, hmw⟩ := h2 ((δ hS (0 + 1) (0 + 1 + 1) rfl).hom w.1)
  have hw : m • w = 0 := by
    apply Subtype.ext
    apply injS
    exact (map_nsmul (δ hS (0 + 1) (0 + 1 + 1) rfl).hom m w.1).trans (hmw.trans (map_zero _).symm)
  have h1' : m • transgression (coindCokernel A) N hN w = 0 := by
    rw [← map_nsmul, hw, map_zero]
  have h2' : ℓ ^ j • transgression (coindCokernel A) N hN w = 0 := by
    apply injQ
    exact (map_nsmul _ (ℓ ^ j) _).trans (hj.trans (map_zero _).symm)
  have h0 := eq_zero_of_coprime_nsmul_of_pow_nsmul hm h1' h2'
  exact (congrArg (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom h0).trans (map_zero _)

section Extension

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem inv_mul_contractNth_mem {n : ℕ} (V : Subgroup G) [V.Normal] (g g' : Fin (n + 1) → G)
    (h : ∀ i, (g i)⁻¹ * g' i ∈ V) (j : Fin (n + 1)) (i : Fin n) :
    (Fin.contractNth j (· * ·) g i)⁻¹ * Fin.contractNth j (· * ·) g' i ∈ V := by
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hij, Fin.contractNth_apply_of_lt _ _ _ _ hij]
    exact h _
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ hij, Fin.contractNth_apply_of_eq _ _ _ _ hij]
    have h1 := h (Fin.castSucc i)
    have h2 := h i.succ
    have h3 : (g i.succ)⁻¹ * ((g (Fin.castSucc i))⁻¹ * g' (Fin.castSucc i)) * g i.succ ∈ V := by
      have := ‹V.Normal›.conj_mem _ h1 (g i.succ)⁻¹
      rwa [inv_inv] at this
    have := mul_mem h3 h2
    convert this using 1
    group
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hij, Fin.contractNth_apply_of_gt _ _ _ _ hij]
    exact h _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem coe_contractNth {N : Subgroup G} {n : ℕ} (j : Fin (n + 1)) (g : Fin (n + 1) → N) (i : Fin n) :
    ((Fin.contractNth j (· * ·) g i : N) : G) = Fin.contractNth j (· * ·) (fun k => (g k : G)) i := by
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ h]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_eq _ _ _ _ h]
    rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h, Fin.contractNth_apply_of_gt _ _ _ _ h]

end Extension

section ExtensionLemma

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

theorem exists_isOpen_cohomologyResLE_eq (N : Subgroup G) (hN : IsClosed (N : Set G)) (n : ℕ)
    (y : cohomology (Rep.res N.subtype A) n) :
    ∃ (H : Subgroup G) (_ : IsOpen (H : Set G)) (hNH : N ≤ H)
      (y' : cohomology (Rep.res H.subtype A) n), (cohomologyResLE A hNH n).hom y' = y := by
  classical
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ n y
  set c : (Fin n → N) → A := cochainOf _ (cocycleι _ n z) with hc_def
  have hc : IsLocallyConstant c := isLocallyConstant_cochainOf _
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hc
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen'
  have hfin : (Set.range c).Finite := hc.range_finite
  set W : Set G := O ∩ ⋂ a ∈ Set.range c, (stabilizer A.ρ a : Set G) with hW
  have hWo : IsOpen W := hO.inter (hfin.isOpen_biInter fun a _ => isOpen_stabilizer A a)
  have hOU' : ∀ m : N, (m : G) ∈ O ↔ m ∈ U := fun m => Set.ext_iff.1 hOU m
  have h1O : (1 : G) ∈ O := by
    have : ((1 : N) : G) ∈ O := (hOU' 1).2 (one_mem U)
    simpa using this
  have h1W : (1 : G) ∈ W := ⟨h1O, Set.mem_iInter₂.2 fun a _ => (stabilizer A.ρ a).one_mem⟩
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  have hVO : ∀ v ∈ (V : Subgroup G), v ∈ O := fun v hv => (hV hv).1
  have hVfix : ∀ v ∈ (V : Subgroup G), ∀ a ∈ Set.range c, A.ρ v a = a := fun v hv a ha =>
    (Set.mem_iInter₂.1 (hV hv).2 a ha)
  set H : Subgroup G := N ⊔ (V : Subgroup G)
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono le_sup_right V.isOpen'
  have hsel : ∀ h : H, ∃ m : N, ((m : G))⁻¹ * h ∈ (V : Subgroup G) := by
    intro h
    obtain ⟨m, hm, v, hv, hmv⟩ := Subgroup.mem_sup_of_normal_right.1 h.2
    exact ⟨⟨m, hm⟩, by rw [← hmv]; simpa using hv⟩
  choose sel hsel using hsel

  have hP : ∀ (x : Fin n → N) (x' : Fin n → N),
      (∀ i, ((x i : G))⁻¹ * x' i ∈ (V : Subgroup G)) → c x = c x' := by
    intro x x' hxx'
    apply hU
    intro i
    exact (hOU' _).1 (hVO _ (by simpa using hxx' i))
  set c' : (Fin n → H) → A := fun h => c (fun i => sel (h i)) with hc'_def
  have hP' : ∀ (x : Fin n → N) (h : Fin n → H),
      (∀ i, ((x i : G))⁻¹ * (h i : G) ∈ (V : Subgroup G)) → c' h = c x := by
    intro x h hxh
    refine (hP x (fun i => sel (h i)) fun i => ?_).symm
    have := mul_mem (hxh i) (inv_mem (hsel (h i)))
    convert this using 1
    group
  have hc' : IsLocallyConstant c' := by
    rw [IsLocallyConstant.iff_exists_open]
    intro h
    refine ⟨⋂ i, (fun h' : Fin n → H => ((h i : G))⁻¹ * (h' i : G)) ⁻¹' (V : Set G),
      isOpen_iInter_of_finite fun i => V.isOpen'.preimage
        (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))),
      Set.mem_iInter.2 fun i => by simp, fun h' hh' => ?_⟩
    have hh'' : ∀ i, ((h i : G))⁻¹ * (h' i : G) ∈ (V : Subgroup G) := fun i => Set.mem_iInter.1 hh' i
    refine (hP' (fun i => sel (h i)) h' fun i => ?_).trans rfl
    have := mul_mem (hsel (h i)) (hh'' i)
    convert this using 1
    group
  have t0 : ∀ h : Fin (n + 1) → H, (Rep.res H.subtype A).ρ (h 0) (c' fun i => h i.succ) =
      (Rep.res N.subtype A).ρ (sel (h 0)) (c fun i => sel (h i.succ)) := by
    intro h
    have hv := hsel (h 0)
    change A.ρ (h 0 : G) (c fun i => sel (h i.succ)) = A.ρ (sel (h 0) : G) (c fun i => sel (h i.succ))
    calc A.ρ (h 0 : G) (c fun i => sel (h i.succ))
        = A.ρ ((sel (h 0) : G) * ((sel (h 0) : G)⁻¹ * h 0)) (c fun i => sel (h i.succ)) := by
          rw [mul_inv_cancel_left]
      _ = A.ρ (sel (h 0) : G) (A.ρ ((sel (h 0) : G)⁻¹ * h 0) (c fun i => sel (h i.succ))) := by
          rw [map_mul]
          rfl
      _ = A.ρ (sel (h 0) : G) (c fun i => sel (h i.succ)) := by
          rw [hVfix _ hv _ ⟨_, rfl⟩]
  have tj : ∀ (h : Fin (n + 1) → H) (j : Fin (n + 1)),
      c' (Fin.contractNth j (· * ·) h) = c (Fin.contractNth j (· * ·) fun i => sel (h i)) := by
    intro h j
    refine hP' _ _ fun i => ?_
    rw [coe_contractNth, coe_contractNth]
    exact inv_mul_contractNth_mem (V : Subgroup G) (fun k => (sel (h k) : G)) (fun k => (h k : G))
      (fun k => hsel (h k)) j i
  have hdc : (inhomogeneousCochains.d (Rep.res H.subtype A) n).hom c' = 0 := by
    have hz := d_cocycleι z
    funext h
    have hz' := congrFun hz (fun i => sel (h i))
    rw [inhomogeneousCochains.d_hom_apply] at hz' ⊢
    rw [t0, Finset.sum_congr rfl fun j _ => by rw [tj h j]]
    exact hz'
  let z' : cocycles (Rep.res H.subtype A) n :=
    (cochainsComplex (Rep.res H.subtype A)).cyclesMk (mkCochain _ c' hc') (n + 1) (by simp) (by
      apply cochainOf_injective (A := Rep.res H.subtype A)
      exact (cochainOf_d _).trans hdc)
  have hz' : cochainOf _ (cocycleι _ n z') = c' :=
    congrArg (cochainOf (Rep.res H.subtype A)) ((cochainsComplex (Rep.res H.subtype A)).i_cyclesMk _ _ _ _)
  refine ⟨H, hHo, le_sup_left, cohomologyπ _ n z', ?_⟩
  rw [cohomologyResLE_eq, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, hz']
  funext g
  exact hP' g (fun i => Subgroup.inclusion le_sup_left (g i)) fun i => by simp

end ExtensionLemma

end GroundTheory.ProfCoh
