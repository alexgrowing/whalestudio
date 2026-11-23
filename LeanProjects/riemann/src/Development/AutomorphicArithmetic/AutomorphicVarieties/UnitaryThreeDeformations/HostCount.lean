import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.DyadicCharacterPowerNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostLocVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.SelmerComplexFiniteAndEulerCharacteristic
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FinrankUnramifiedCocyclesEqFinrankInvariants
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LocalEulerCharacteristicRationals
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalCohomologyFiniteSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsAbsGaloisFixingSqrtNegOneCyclotomicNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FinrankGradedPieceAndComplexConjugationInvariant
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HcAvg

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

section Abs

variable {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M] [Module.Finite k M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M)

private theorem rank_coboundaries_invariants : finrank k (B1 ρ) + finrank k (H0 ρ) = finrank k M := by
  have h : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp [sub_eq_zero]
  rw [← h]
  exact LinearMap.finrank_range_add_finrank_ker (d0 ρ)

private theorem rank_cocycles_formula (h : ContAction ρ) [Module.Finite k (H1 ρ)] :
    finrank k (Z1 ρ) + finrank k (H0 ρ) = finrank k (H1 ρ) + finrank k M := by
  have e := Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles ρ h)
  haveI : Module.Finite k (B1 ρ) := Module.Finite.range (d0 ρ)
  haveI : Module.Finite k ((B1 ρ).comap (Z1 ρ).subtype) := Module.Finite.equiv e.symm
  haveI : Module.Finite k (Z1 ρ) := Module.Finite.of_submodule_quotient ((B1 ρ).comap (Z1 ρ).subtype)
  rw [← Submodule.finrank_quotient_add_finrank ((B1 ρ).comap (Z1 ρ).subtype), e.finrank_eq, ← rank_coboundaries_invariants ρ]
  ring

private theorem invariants_zero_of_scalar {x : D} {a : k} (hx : ∀ m, ρ x m = a • m) (ha : a ≠ 1) : finrank k (H0 ρ) = 0 := by
  rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  intro m hm
  have h : (a - 1) • m = 0 := by rw [sub_smul, ← hx, hm x, one_smul, sub_self]
  exact (smul_eq_zero.1 h).resolve_left (sub_ne_zero.2 ha)

end Abs

private theorem hc_avg {k D M : Type} [Field k] [Group D] [AddCommGroup M] [Module k M] (ρ : Representation k D M)
    (N : Subgroup D) (hN : ((N.index : ℕ) : k) ≠ 0) (z : D → M) (hz : ∀ g h, z (g * h) = z g + ρ g (z h))
    (h0 : ∀ s ∈ N, z s = 0) : ∃ m, ∀ g, z g = ρ g m - m :=
  _root_.UpperTheory.Reformulated.B.Qe18.hc_avg ρ N hN z hz h0

private theorem hc_tame :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (I N : Subgroup D) (W : Submodule k (D → M)), ContAction ρ → I.Normal → (∃ φ : D, (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
    N ≤ I → (N.subgroupOf I).Normal → ((N.relIndex I : ℕ) : k) ≠ 0 → (∀ s ∈ N, ∀ m, ρ s m = m) →
    (∀ y, y ∈ W ↔ y ∈ Z1 ρ ∧ ∀ s ∈ N, y s = 0) → finrank k W = finrank k M := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ I N W hρ hI hφ hNI _ hidx hN hW
  let r : W →ₗ[k] (I → M) := (LinearMap.funLeft k M I.subtype).comp W.subtype
  have hr : LinearMap.range r = B1 (ρ.comp I.subtype : Representation k I M) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z1, z2⟩ := (hW _).1 z.2
      exact (mem_coboundaries1 _ _).2 (hc_avg (ρ.comp I.subtype) (N.subgroupOf I) hidx _ (fun g h => z1.2 g h) fun s hs => z2 s hs)
    · rintro ⟨m, rfl⟩
      exact ⟨⟨d0 ρ m, (hW _).2 ⟨coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩, fun s hs => by rw [amitsur_d0_apply, hN s hs, sub_self]⟩⟩, rfl⟩
  have hk := UpperTheory.finrank_unramified_cocycles_eq_finrank_invariants ρ I ((LinearMap.ker r).map W.subtype) hρ hI hφ fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; exact ⟨((hW _).1 z.2).1, fun s hs => congrFun hz ⟨s, hs⟩⟩,
      fun h => ⟨⟨y, (hW _).2 ⟨h.1, fun s hs => h.2 s (hNI hs)⟩⟩, funext fun s => h.2 s s.2, rfl⟩⟩
  rw [Submodule.finrank_map_subtype_eq] at hk
  obtain ⟨φ, hφ, -⟩ := hφ
  haveI : Module.Finite k (B1 (ρ.comp I.subtype : Representation k I M)) := Module.Finite.range _
  haveI : Module.Finite k W := by
    let r' : W →ₗ[k] B1 (ρ.comp I.subtype : Representation k I M) := r.codRestrict _ fun z => hr ▸ ⟨z, rfl⟩
    refine Module.Finite.of_injective (r'.prod ((LinearMap.proj φ).comp W.subtype)) ?_
    rw [injective_iff_map_eq_zero]
    intro z hz
    have z1 := ((hW _).1 z.2).1
    have e1 : r z = 0 := congrArg (fun p => p.1.1) hz
    have e2 : z.1 φ = 0 := congrArg Prod.snd hz
    have o : z.1 1 = 0 := by simpa using z1.2 1 1
    let K : Subgroup D :=
      { carrier := {g | z.1 g = 0}
        one_mem' := o
        mul_mem' := fun {a b} ha hb => by
          show z.1 _ = 0
          rw [z1.2, show z.1 a = 0 from ha, show z.1 b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := z1.2 a⁻¹ a
          rw [inv_mul_cancel, o, show z.1 a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hK := Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers φ) (t := K)
      (sup_le (fun s hs => congrFun e1 ⟨s, hs⟩) (Subgroup.zpowers_le.2 e2)) (isClosed_eq z1.1 continuous_const)
    rw [hφ] at hK
    exact Subtype.ext (funext fun g => hK (Subgroup.mem_top g))
  rw [← LinearMap.finrank_range_add_finrank_ker r, hr, hk]
  exact rank_coboundaries_invariants _

private theorem hc_val {k : Type} [CommRing k] {j : ℤ} {X Y : Gb k j} (h : X.val = Y.val) : X = Y := Subtype.ext h

private theorem hc_scal {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) {g : D} (hg : η g = 1)
    (X : Gb k j) : gRep η Ψ j g X = ((Ψ g ^ j : kˣ) : k) • X := by
  refine hc_val ?_
  ext a b
  rw [gRep_val, adRep_baseLift_apply, if_pos hg]
  show _ = ((Ψ g ^ j : kˣ) : k) * X.val a b
  by_cases h : wt a b = j
  · rw [h]
  · have : X.val a b = 0 := X.2 a b h
    simp [this]

private theorem hc_congr {k D : Type} [CommRing k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (j : ℤ) {g g' : D}
    (h : η g = η g') (h' : Ψ g ^ j = Ψ g' ^ j) (X : Gb k j) : gRep η Ψ j g X = gRep η Ψ j g' X := by
  rcases Int.units_eq_one_or (η g) with h1 | h1
  · rw [hc_scal η Ψ j h1, hc_scal η Ψ j (h ▸ h1), h']
  · refine hc_val ?_
    ext a b
    have h2 : ¬ η g = 1 := by rw [h1]; decide
    rw [gRep_val, gRep_val, adRep_baseLift_apply, adRep_baseLift_apply, if_neg h2, if_neg (h ▸ h2)]
    by_cases e : wt a b = j
    · rw [e, h']
    · have : X.val b.rev a.rev = 0 := X.2 _ _ (by
        have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
        rwa [this])
      simp [this]

private theorem hc_pow {k : Type} [Field k] {a : kˣ} (ha : (a : k) ^ 2 - 1 ≠ 0) {j : ℤ} (h0 : j ≠ 0) (h2 : |j| ≤ 2) :
    ((a ^ j : kˣ) : k) ≠ 1 := by
  intro h
  have h1 : a ^ j = 1 := Units.ext h
  have h3 : a ^ (2 : ℤ) = 1 := by
    have : j ∣ 2 := by
      rw [abs_le] at h2
      obtain ⟨h2, h3⟩ := h2
      interval_cases j <;> first | decide | exact absurd rfl h0
    obtain ⟨c, hc⟩ := this
    rw [hc, _root_.zpow_mul, h1, _root_.one_zpow]
  apply ha
  rw [sub_eq_zero]
  have h4 : a ^ 2 = 1 := by exact_mod_cast h3
  rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]

section Fr

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] {G Γ ι : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {F : Frame O G Γ ι}

private theorem hc_two (hF : F.Ok) : (2 : ResidueField O) ≠ 0 := by
  have h := hF.two.map (residue O)
  rw [map_ofNat] at h
  exact h.ne_zero

private theorem hc_c (hF : F.Ok) : F.Ψbar F.c = 1 := by simp [Frame.Ψbar, hF.Ψc]

private theorem hc_cont (hF : F.Ok) (j : ℤ) : ContAction (F.gbar j) := by
  have h1 : IsLocallyConstant F.Ψbar := by
    refine IsLocallyConstant.desc _ Units.val ?_ Units.val_injective
    have := (hF.Ψ_cont 1).comp (Ideal.Quotient.factor (le_of_eq (pow_one (maximalIdeal O))))
    exact this
  have h2 := (hF.η_cont.prodMk h1).comp_continuous (continuous_fst (Y := Gb (ResidueField O) j))
  have h3 : IsLocallyConstant (Prod.snd : Γ × Gb (ResidueField O) j → _) :=
    (IsLocallyConstant.iff_continuous _).2 continuous_snd
  have h4 := (h2.prodMk h3).comp fun q => gRep (MonoidHom.fst ℤˣ (ResidueField O)ˣ) (MonoidHom.snd _ _) j q.1 q.2
  exact h4.continuous

private theorem exists_scalar_action_nontrivial (hF : F.Ok) {j : ℤ} (hj : j ≠ 0) {x : Γ} (h1 : F.η x = 1) (h2 : IsUnit ((F.Ψ x : O) ^ 2 - 1)) :
    ∃ a : ResidueField O, (∀ m, F.gbar j x m = a • m) ∧ a ≠ 1 := by
  by_cases h : |j| ≤ 2
  · refine ⟨_, hc_scal _ _ j h1, hc_pow ?_ hj h⟩
    have := (h2.map (residue O)).ne_zero
    rw [map_sub, map_pow, map_one] at this
    exact this
  · obtain ⟨f, e, -⟩ := UpperTheory.finrank_gradedPiece_and_complexConjugation_invariants F.η F.Ψbar F.c (hc_two hF) hF.ηc (hc_c hF) j
    have : Subsingleton (Gb (ResidueField O) j) := by
      rw [← Module.finrank_zero_iff (R := ResidueField O), e]; omega
    exact ⟨0, fun m => Subsingleton.elim _ _, zero_ne_one⟩

private theorem hc_N (j : ℤ) (v : ι) (s : F.D v) (hs : s ∈ F.Nv v) (m : Gb (ResidueField O) j) : F.gloc j v s m = m := by
  have h : F.Ψbar (F.loc v s) = 1 := hs.2
  have := hc_scal F.η F.Ψbar j (g := F.loc v s) hs.1.2 m
  rw [h] at this
  simpa using this

private theorem hc_I (hF : F.Ok) (s : F.D F.vl) (hs : s ∈ F.Iv F.vl) (m : Gb (ResidueField O) 0) :
    F.gloc 0 F.vl s m = m := by
  have := hc_scal F.η F.Ψbar 0 (g := F.loc _ s) (hF.η_I _ (Or.inl rfl) s hs) m
  simpa using this

private theorem hc_contv (hF : F.Ok) (j : ℤ) (v : ι) : ContAction (F.gloc j v) := by
  have h : Continuous fun p : F.D v × Gb (ResidueField O) j => (F.loc v p.1, p.2) :=
    ((hF.π_cont.comp continuous_subtype_val).comp continuous_fst).prodMk continuous_snd
  have h2 : Continuous fun p : Γ × Gb (ResidueField O) j => F.gbar j p.1 p.2 := hc_cont hF j
  have h3 := h2.comp h
  exact h3

private theorem hc_B (hF : F.Ok) (j : ℤ) (v : ι) : B1 (F.gloc j v) ≤ F.ZL j v := by
  intro y hy
  refine ⟨coboundaries_le_cocycles _ (hc_contv hF j v) hy, fun _ s hs => ?_, fun _ _ => hy, fun e e' s hs => ?_⟩
  · obtain ⟨m, rfl⟩ := hy
    rw [amitsur_d0_apply, hc_N j v s hs, sub_self]
  · subst e e'
    obtain ⟨m, rfl⟩ := hy
    rw [amitsur_d0_apply, hc_I hF s hs, sub_self]

private theorem hc_idx (hF : F.Ok) (v : ι) : ((F.Nv v).subgroupOf (F.Iv v)).Normal ∧
    (((F.Nv v).relIndex (F.Iv v) : ℕ) : ResidueField O) ≠ 0 := by
  have e : (F.Nv v).subgroupOf (F.Iv v) = (((F.η.prod F.Ψbar).comp (F.loc v)).comp (F.Iv v).subtype).ker := by
    ext s
    exact ⟨fun h => Prod.ext h.1.2 h.2, fun h => ⟨⟨s.2, congrArg Prod.fst h⟩, congrArg Prod.snd h⟩⟩
  rw [Subgroup.relIndex, e]
  refine ⟨inferInstance, fun h => ?_⟩
  rw [Subgroup.index_ker] at h
  obtain ⟨t, ht⟩ := Subgroup.card_subgroup_dvd_card (((F.η.prod F.Ψbar).comp (F.loc v)).comp (F.Iv v).subtype).range
  have h2 := congrArg (Nat.cast (R := ResidueField O)) ht
  letI := Fintype.ofFinite (ResidueField O)
  rw [Nat.cast_mul, h, zero_mul, Nat.card_prod, Nat.card_units (ResidueField O), Nat.cast_mul,
    Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card (α := ResidueField O), FiniteField.cast_card_eq_zero,
    Nat.card_eq_fintype_card, Fintype.card_units_int] at h2
  exact hc_two hF (by simpa using h2)

private theorem hc_count [Fintype ι] (hF : F.Ok) (hV : F.LocVan) (j : ℤ)
    (g1 : Module.Finite (ResidueField O) (H1 (F.gbar j))) (g2 : Module.Finite (ResidueField O) (H2 (F.gbar j)))
    (g3 : finrank (ResidueField O) (H1 (F.gbar j)) + finrank (ResidueField O) (LinearMap.ker (F.gbar j F.c - LinearMap.id)) =
      finrank (ResidueField O) (H0 (F.gbar j)) + finrank (ResidueField O) (H2 (F.gbar j)) +
        finrank (ResidueField O) (Gb (ResidueField O) j))
    (l1 : ∀ v, Module.Finite (ResidueField O) (H1 (F.gloc j v))) (l2 : ∀ v, Module.Finite (ResidueField O) (H2 (F.gloc j v)))
    (l3 : finrank (ResidueField O) (H1 (F.gloc j F.vl)) = finrank (ResidueField O) (H0 (F.gloc j F.vl)) +
      finrank (ResidueField O) (H2 (F.gloc j F.vl)) + finrank (ResidueField O) (Gb (ResidueField O) j))
    (l4 : ∀ v ≠ F.vl, finrank (ResidueField O) (H1 (F.gloc j v)) = finrank (ResidueField O) (H0 (F.gloc j v)) +
      finrank (ResidueField O) (H2 (F.gloc j v)))
    (hs : ∀ κ : ∀ v, Z2 (F.gloc j v), ∃ z : Z2 (F.gbar j), ∀ v, F.res2 j v z.1 - (κ v).1 ∈ B2 (F.gloc j v)) :
    Module.Finite (ResidueField O) (F.selmerCohomologyQuotient j) ∧ Module.Finite (ResidueField O) (F.Ob j) ∧
      (finrank (ResidueField O) (F.selmerCohomologyQuotient j) : ℤ) - finrank (ResidueField O) (F.Ob j) = Frame.defect j := by
  obtain ⟨f, d1, d2⟩ := UpperTheory.finrank_gradedPiece_and_complexConjugation_invariants F.η F.Ψbar F.c (hc_two hF) hF.ηc (hc_c hF) j
  haveI : Finite (Gb (ResidueField O) j) := Module.finite_of_finite (ResidueField O)
  obtain ⟨c1, c2, c3⟩ := UpperTheory.selmerComplex_finite_and_euler_characteristic F j hF.π_cont (hc_cont hF j) f (hc_B hF j) g1 g2 l1 l2 hs
  refine ⟨c1, c2, ?_⟩
  have z := fun v => rank_cocycles_formula _ (hc_contv hF j v)
  rw [c3, Finset.sum_eq_single F.vl (fun v _ hv => ?_) (fun h => (h (Finset.mem_univ _)).elim)]
  swap
  · have := hc_tame (F.gloc j v) (F.Iv v) (F.Nv v) (F.ZL j v) (hc_contv hF j v) (hF.I_normal v) (hF.frob v)
      (fun s hs => hs.1.1) (hc_idx hF v).1 (hc_idx hF v).2 (hc_N j v)
      (fun y => ⟨fun h => ⟨h.1, h.2.1 hv⟩, fun h => ⟨h.1, fun _ => h.2, fun e => (hv e).elim, fun e => (hv e).elim⟩⟩)
    have := z v
    have := l4 v hv
    omega
  have zl := z F.vl
  have d3 : finrank (ResidueField O) (LinearMap.ker (F.gbar j F.c - LinearMap.id)) = if |j| ≤ 1 then 1 else 0 := d2
  obtain ⟨x, x1, x2⟩ := hF.x F.vl (Or.inl rfl)
  have h0 : j ≠ 0 → finrank (ResidueField O) (H0 (F.gbar j)) = 0 ∧ finrank (ResidueField O) (H0 (F.gloc j F.vl)) = 0 :=
    fun hj => by
      obtain ⟨a, a1, a2⟩ := exists_scalar_action_nontrivial hF hj x1 x2
      exact ⟨invariants_zero_of_scalar _ a1 a2, invariants_zero_of_scalar (F.gloc j F.vl) (x := x) a1 a2⟩
  unfold Frame.defect
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · have e : F.ZL j F.vl = B1 (F.gloc j F.vl) := le_antisymm (fun y hy => hy.2.2.1 rfl hj) (hc_B hF j _)
    have := rank_coboundaries_invariants (F.gloc j F.vl)
    have := h0 hj.ne
    rw [e]
    rw [abs_of_neg hj] at d3
    split_ifs at d3 ⊢ <;> omega
  · have := hc_tame (F.gloc 0 F.vl) (F.Iv _) (F.Iv _) (F.ZL 0 F.vl) (hc_contv hF 0 _) (hF.I_normal _) (hF.frob _)
      le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) (by simp) (hc_I hF)
      (fun y => ⟨fun h => ⟨h.1, h.2.2.2 rfl rfl⟩, fun h => ⟨h.1, fun e => (e rfl).elim, fun _ e => (lt_irrefl _ e).elim,
        fun _ _ => h.2⟩⟩)
    have e : H0 (F.gbar 0) = LinearMap.ker (F.gbar 0 F.c - LinearMap.id) := by
      ext m
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]
      refine ⟨fun h => h _, fun h g => ?_⟩
      rcases Int.units_eq_one_or (F.η g) with h1 | h1
      · simpa using hc_scal F.η F.Ψbar 0 h1 m
      · exact (hc_congr F.η F.Ψbar 0 (h1.trans hF.ηc.symm) (by simp) m).trans h
    rw [e] at g3
    simp only [show ¬ (0 : ℤ) = -1 by decide, show ¬ ((0 : ℤ) = 1 ∨ (0 : ℤ) = 2) by decide, if_false]
    omega
  · have e : F.ZL j F.vl = Z1 (F.gloc j F.vl) := le_antisymm (fun y hy => hy.1) fun y hy =>
      ⟨hy, fun e => (e rfl).elim, fun _ e => (lt_asymm hj e).elim, fun _ e => (hj.ne' e).elim⟩
    have := hV.h2 F.vl (Or.inl rfl) j hj.ne'
    have : finrank (ResidueField O) (H2 (F.gloc j F.vl)) = 0 := Module.finrank_zero_of_subsingleton
    have := h0 hj.ne'
    rw [e]
    rw [abs_of_pos hj] at d1 d3
    split_ifs at d3 ⊢ <;> omega

end Fr

theorem UpperTheory.V.UnitaryThreeInertia.hostFrame_count :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    F.Count := by
  intro hLF hLT hLE hGF hGE hPT Ω _ _ _ l hl c N _ e ψ o₁ hd S A F hF j
  have hO := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hV := hostFrame_locVan hLF hLT hLE Ω c e ψ o₁ hd S A F hF
  obtain ⟨x, x1, x2, x3⟩ := exists_sigma Ω c e ψ o₁ hd S A F hF F.vl (Or.inl rfl)
  have hS : ContainsAbove S l := fun v hv => (hF.mem v).2 (by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    rw [← map_natCast (residue c.O), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] c.O), mem_maximalIdeal,
      mem_nonunits_iff, isUnit_map_iff, PadicInt.isUnit_iff, PadicInt.norm_p]
    exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)).ne
  obtain ⟨f, -⟩ := UpperTheory.finrank_gradedPiece_and_complexConjugation_invariants F.η F.Ψbar F.c (hc_two hO) hO.ηc (hc_c hO) j
  haveI : Finite (Gb (ResidueField c.O) j) := Module.finite_of_finite (ResidueField c.O)
  have hσ : ∃ (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (a : ResidueField c.O) (n : ℕ), (∀ m, F.gbar j (F.π σ) m = a • m) ∧
      (n : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) ∧ a ≠ (n : ResidueField c.O) := by
    by_cases hj : j = 0
    · subst hj
      obtain ⟨σ, s1, s2⟩ := UpperTheory.exists_absGalois_fixing_sqrt_neg_one_cyclotomic_ne_one Ω l hd.l_odd
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      refine ⟨σ, 1, _, fun m => ?_, ZMod.natCast_zmod_val _, fun h => s2 (Units.ext ?_)⟩
      · simpa using hc_scal F.η F.Ψbar 0 ((DFunLike.congr_fun hF.η σ).trans s1) m
      · rw [← Nat.cast_one, CharP.natCast_eq_natCast _ l] at h
        rw [← ZMod.natCast_zmod_val (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ).val, Units.val_one, ← Nat.cast_one (R := ZMod (l ^ 1)),
          ZMod.natCast_eq_natCast_iff]
        simpa only [pow_one] using h.symm
    · obtain ⟨a, a1, a2⟩ := exists_scalar_action_nontrivial hO hj x1 x2
      exact ⟨x, a, 1, a1, by rw [x3]; simp, by simpa using a2⟩
  have hv : ∀ v : S, ((l : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.1.asIdeal → v = F.vl := fun v hv => by
    have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have e : ((l : ℕ) : NumberField.RingOfIntegers ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    have hp : Prime ((l : ℕ) : NumberField.RingOfIntegers ℚ) := by
      rw [e]
      exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
    have hm : (Ideal.span {((l : ℕ) : NumberField.RingOfIntegers ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal (by simpa using hl.out.ne_zero)
    refine Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)
    rw [← hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv),
      ← hm.eq_of_le F.vl.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hF.vl)]
  obtain ⟨σ, hcc, hc⟩ := hF.cc
  have hcont := hc_cont hO j
  have hcv := hc_contv hO j
  have key := hc_count hO hV j
  have hvl := hF.vl
  have hA := hF.isOver
  have hπ := hF.π
  have hD : F.D = fun v => Dec (F := ℚ) (A v) := funext hF.D
  rw [← hc] at key
  clear hO hV x1 x2 x3 x hF hc
  obtain ⟨π, η, Ψ, cc, D, I, vl, Sb⟩ := F
  dsimp only at hπ hD
  subst hπ hD
  obtain ⟨g1, g2, g3⟩ := UpperTheory.global_euler_characteristic_rationals_odd_prime hGF hGE Ω l hd.l_odd _ _ S _ hS hcont σ hcc
  have L := fun v : S => UpperTheory.local_euler_characteristic_rationals hLF hLE Ω l _ _ (A v) v.1 _ (hA v) (hcv v)
  exact key g1 g2 g3 (fun v => (L v).1) (fun v => (L v).2.1) ((L vl).2.2.1 hvl)
    (fun v h => (L v).2.2.2 fun h' => h (hv v h')) (UpperTheory.global_cohomology_finite_set hPT Ω l hd.l_odd _ _ S A _ hS hA hcont hσ)
