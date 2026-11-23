import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenCokerLe

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_pi {R Z M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [Fintype ι] (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (W : Submodule R Z) (H : ι → Submodule R M)
    (hW : ∀ z ∈ W, ∀ i, ev z i ∈ H i) : Module.length R W ≤ ∑ i, Module.length R (H i) := by
  rw [← Module.length_pi_of_fintype]
  let φ : W →ₗ[R] (∀ i, H i) := LinearMap.pi fun i =>
    LinearMap.codRestrict (H i) ((LinearMap.proj i).comp (ev.comp W.subtype)) fun z => hW z.1 z.2 i
  refine Module.length_le_of_injective φ fun x y hxy => ?_
  refine Subtype.ext (hev (funext fun i => ?_))
  exact congrArg Subtype.val (congrFun hxy i)

private theorem len_abs {R Z K M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Fintype ι] (hM : ∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤)
    (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (π : Z →ₗ[R] K) (hπ : Function.Surjective π) (a : R)
    (ha : ∀ z, π (a • z) = 0) (H : Submodule R M) (hH : ∀ m, a • m = 0 → m ∈ H) :
    Module.length R K ≤ Fintype.card ι * Module.length R H := by
  have hZ : ∀ z : Z, Module.length R (Submodule.span R {z}) ≠ ⊤ := by
    intro z
    refine ne_top_of_le_ne_top ?_ (len_le_pi ev hev _ (fun i => Submodule.span R {ev z i}) ?_)
    · exact ENat.sum_ne_top.2 fun i _ => hM _
    · intro w hw i
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := lenCokerLe R Z hZ a
  have h2 := len_le_pi ev hev (LinearMap.ker (a • (LinearMap.id : Z →ₗ[R] Z))) (fun _ => H) (by
    intro z hz i
    apply hH
    have : a • z = 0 := hz
    have e := congrFun (congrArg ev this) i
    simpa using e)
  have h3 : Module.length R K ≤ Module.length R (Z ⧸ LinearMap.range (a • (LinearMap.id : Z →ₗ[R] Z))) := by
    refine Module.length_le_of_surjective (Submodule.liftQ _ π ?_) ?_
    · rintro _ ⟨z, rfl⟩
      exact ha z
    · intro k
      obtain ⟨z, rfl⟩ := hπ k
      exact ⟨Submodule.Quotient.mk z, rfl⟩
  refine h3.trans (h1.trans (h2.trans ?_))
  simp

theorem UpperTheory.V.Base.kerResAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [IsPrincipalIdealRing R], ContAction ρ → (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ T : Finset G, (T : Set G) ⊆ U →
      U ≤ (Subgroup.closure (T : Set G) ⊔ U').topologicalClosure →
      Module.length R (LinearMap.ker (resU ρ h)) ≤ T.card * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ hρ hM hc U' U h hab T hT hU
  choose c hc using hc
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Z0 : Submodule R (Z1U ρ U) :=
    { carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun {x y} hx hy u hu => by
        show x.1 u + y.1 u = 0
        rw [hx u hu, hy u hu, add_zero]
      smul_mem' := fun r x hx u hu => by
        show r • x.1 u = 0
        rw [hx u hu, smul_zero] }
  have hcoc : ∀ (z : Z1U ρ U) (u v : U), z.1 (u * v) = z.1 u + ρ u (z.1 v) := fun z u v => z.2.2 u v
  let ev : Z0 →ₗ[R] (T → M) := LinearMap.pi fun t =>
    (LinearMap.proj (⟨t.1, hT t.2⟩ : U)).comp ((Z1U ρ U).subtype.comp Z0.subtype)
  have hev : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : z.1.1 1 = 0 := z.2 1 U'.one_mem
    let K : Subgroup U :=
      { carrier := {u | z.1.1 u = 0}
        one_mem' := h1
        mul_mem' := fun {u v} hu hv => by
          have hu' : z.1.1 u = 0 := hu
          have hv' : z.1.1 v = 0 := hv
          show z.1.1 (u * v) = 0
          rw [hcoc, hu', hv', map_zero, add_zero]
        inv_mem' := fun {u} hu => by
          have hu' : z.1.1 u = 0 := hu
          have e := hcoc z.1 u⁻¹ u
          rw [inv_mul_cancel, h1, hu', map_zero, add_zero] at e
          exact e.symm }
    have hK : IsClosed (K : Set U) := isClosed_eq z.1.2.1 continuous_const
    have hle : Subgroup.closure (T : Set G) ⊔ U' ≤ K.map U.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 fun t ht => ?_) fun u hu => ?_
      · exact ⟨⟨t, hT ht⟩, congrFun hz ⟨t, ht⟩, rfl⟩
      · exact ⟨⟨u, h hu⟩, z.2 _ hu, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun u => ?_))
    have : u ∈ closure (K : Set U) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact closure_mono hle (hU u.2)
    rw [hK.closure_eq] at this
    exact this
  let π : Z0 →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _ ((Submodule.mkQ _).comp Z0.subtype) fun z =>
      (resU_mk_eq_zero ρ h z.1).2 ⟨0, fun u => by rw [z.2 _ u.2]; simp⟩
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
    let b : Z1U ρ U := ⟨d0 _ m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩
    refine ⟨⟨z - b, fun u hu => ?_⟩, Subtype.ext ?_⟩
    · show z.1 u - (ρ u m - m) = 0
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · refine (mk_eq_mk ρ U (z - b) z).2 ⟨-m, fun u => ?_⟩
      show z.1 u - (ρ u m - m) - z.1 u = _
      rw [map_neg]
      abel
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range fun u : U => c u - 1))).principal
  have hkill : ∀ (u : U) (z : Z0), π ((c u - 1) • z) = 0 := by
    intro u z
    refine Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨z.1.1 u, fun g => ?_⟩))
    show (c u - 1) • z.1.1 g = ρ g (z.1.1 u) - z.1.1 u
    have e0 : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
    have e1 : ρ ((u * g * u⁻¹ * g⁻¹ : U) : G) = 1 := by
      have : ρ u * ρ g = ρ g * ρ u := by
        ext m
        simp only [Module.End.mul_apply, hc, smul_smul, mul_comm]
      have e : ((u * g * u⁻¹ * g⁻¹ : U) : G) = u * g * ((u : G)⁻¹ * (g : G)⁻¹) := by
        simp [mul_assoc]
      rw [e, map_mul, map_mul, this, ← map_mul, ← map_mul]
      simp
    have e2 : z.1.1 (u * g) = z.1.1 (g * u) := by
      rw [e0, hcoc, e1, z.2 _ (hab u u.2 g g.2)]
      simp
    rw [hcoc, hcoc, hc u] at e2
    rw [sub_smul, one_smul, eq_sub_of_add_eq' e2]
    abel
  have hamem : a ∈ Ideal.span (Set.range fun u : U => c u - 1) := by
    rw [ha]; exact Submodule.mem_span_singleton_self a
  have key := len_abs hM ev hev π hπ a (fun z => ?_) (H0U ρ U) (fun m hm => ?_)
  · simpa using key
  · refine Submodule.span_induction (p := fun r _ => π (r • z) = 0) ?_ ?_ ?_ ?_ hamem
    · rintro _ ⟨u, rfl⟩
      exact hkill u z
    · simp
    · intro x y _ _ hx hy
      rw [add_smul, map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_assoc, map_smul, hx, smul_zero]
  · intro u
    have : c u - 1 ∈ Ideal.span (Set.range fun u : U => c u - 1) := Ideal.subset_span ⟨u, rfl⟩
    rw [ha] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    show ρ u m = m
    have e : (c u - 1) • m = 0 := by rw [← hr, smul_assoc, hm, smul_zero]
    rw [hc, ← sub_eq_zero]
    rw [sub_smul, one_smul] at e
    exact e
