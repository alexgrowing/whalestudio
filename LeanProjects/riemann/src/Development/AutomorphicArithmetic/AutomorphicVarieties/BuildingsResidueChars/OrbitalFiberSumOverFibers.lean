import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition

open MulAction

private theorem conj_memS {G : Type} [Group G] {S : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {s : G} (hs : s ∈ S) (a : G) : a * s * a⁻¹ ∈ S := by
  have h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
  rw [h]
  exact S.mul_mem (hc a s) hs

private theorem mem_orb {G : Type} [Group G] (S U : Subgroup G) (x : G) (y : G ⧸ U) :
    y ∈ orbit S (x : G ⧸ U) ↔ ∃ s ∈ S, y = ((s * x : G) : G ⧸ U) := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

private theorem sup_act {G : Type} [Group G] {S U : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {g : G} (hg : g ∈ S ⊔ U) (x : G) {y : G ⧸ U} (hy : y ∈ orbit S (x : G ⧸ U)) :
    g • y ∈ orbit S (x : G ⧸ U) := by
  haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
  obtain ⟨s, hs, u, hu, rfl⟩ := hg
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_orb S U x y).1 hy
  refine (mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩
  · convert S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1
    group
  · rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    convert U.inv_mem hu using 1
    group

private theorem phi_out {G : Type} [Group G] (U : Subgroup G) (Φ : G → ℂ) (hΦu : ∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) (g : G) :
    Φ ((g : G ⧸ U).out) = Φ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hΦu _ u.2]

theorem UpperTheory.orbitalFiber_sum_over_fibers :
    UpperTheory.V.Z.Sym.Glob.Fib.SumFib := by
  intro Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov
  classical
  let Γ' : Subgroup Γ := Subgroup.comap ι (S ⊔ U')
  letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι
  letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)
  let k : G ⧸ U' → ℂ := fun y => Φ y.out
  let ki : I → G ⧸ U' → ℂ := fun i => (orbit S (x i : G ⧸ U')).indicator k
  have hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U') := fun h g => rfl
  have hk : ∀ g : G, k g = Φ g := phi_out U' Φ hΦu
  have hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y := by
    intro h y
    refine QuotientGroup.induction_on y fun g => ?_
    rw [hsmul, hk, hk, hΦl]
  have hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U') :=
    fun i y h => Set.mem_of_indicator_ne_zero h
  have hD := @UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U')
    (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv
    ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_
  · show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)
    rw [hD, finsum_eq_sum_of_fintype]
    rfl
  · obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩
    refine QuotientGroup.induction_on y fun g _ => ?_
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
    refine ⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hsmul, QuotientGroup.eq]
    convert U'.inv_mem hu using 1
    group
  · intro i h y
    have hh : ι h ∈ S ⊔ U' := h.2
    have e : h • y = (ι h) • y := rfl
    have hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U') := by
      rw [e]
      constructor
      · intro hy'
        simpa using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'
      · intro hy
        exact sup_act hc hh (x i) hy
    show Set.indicator _ k (h • y) = Set.indicator _ k y
    by_cases hy : y ∈ orbit S (x i : G ⧸ U')
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]
      exact hkinv (h : Γ) y
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]
  · intro i y h
    exact (Set.indicator_of_mem (hki_mem i y h) k).symm
  · intro z
    refine QuotientGroup.induction_on z fun g hz => ?_
    obtain ⟨i, γ, s, hs, u, hu, rfl⟩ := hcov g
    have hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U') := (mem_orb S U' _ _).2 ⟨s, hs, rfl⟩
    have hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U') := by
      rw [hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]
    refine ⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩
    · rw [show ki i _ = k _ from Set.indicator_of_mem hy k, hval]
      exact hz
    · show _ = γ • ((s * x i : G) : G ⧸ U')
      rw [hsmul, QuotientGroup.eq]
      convert U'.inv_mem hu using 1
      group
  · intro i j y y' h hy hy' he
    obtain ⟨s, hs, rfl⟩ := (mem_orb S U' _ _).1 (hki_mem i y hy)
    obtain ⟨s', hs', rfl⟩ := (mem_orb S U' _ _).1 (hki_mem j y' hy')
    change ((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he
    rw [QuotientGroup.eq] at he
    obtain ⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u := ⟨_, he, rfl⟩
    have hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u := by
      rw [← hu_eq]
      group
    have e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹ := by
      rw [← hu_eq]
      group
    have hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S :=
      S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs
    have key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U' := by
      intro X
      have e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹ := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs')
        (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem)))
        (Subgroup.mem_sup_left (S.inv_mem hs))
    have hij := hdisj i j h _ hmid u hu_mem hxj
    subst hij
    refine ⟨rfl, ⟨h, ?_⟩, rfl⟩
    show ι h ∈ S ⊔ U'
    rw [e2]
    exact key _
