import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orb_gen {G O : Type} [CommGroup G] [Finite G] [CommRing O] [IsDomain O] (f : G →* Oˣ) :
    IsCyclic (G ⧸ f.ker) ∧ ∃ g : G, (∀ x, ∃ a : ℕ, f x = f g ^ a) ∧ f.ker.index = orderOf (f g) := by
  have hfin : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have hc : IsCyclic f.range := isCyclic_subgroup_units f.range
  refine ⟨isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange f).symm
    (QuotientGroup.quotientKerEquivRange f).symm.surjective, ?_⟩
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := hc.exists_monoid_generator
  refine ⟨g, fun x => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hg ⟨f x, x, rfl⟩
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · rw [Subgroup.index_ker, ← orderOf_eq_card_of_forall_mem_powers hg, ← Subgroup.orderOf_coe]

theorem UpperTheory.V.HV.orbFacts :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (ψ : DirichletCharacter O N), ψ.toUnitHom.ker.index = orderOf ψ ∧ IsCyclic ((ZMod N)ˣ ⧸ ψ.toUnitHom.ker) ∧
      (∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker ↔ ∃ j : ℕ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j) ∧
      {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker}.ncard = Nat.totient (orderOf ψ) := by
  intro O _ _ N _ ψ
  obtain ⟨hc, g, hg, hidx⟩ := orb_gen ψ.toUnitHom
  have hpow : ∀ (χ : DirichletCharacter O N) (k : ℕ) (x : (ZMod N)ˣ),
      (χ ^ k).toUnitHom x = χ.toUnitHom x ^ k := by
    intro χ k x
    ext
    simp [MulChar.pow_apply_coe]
  have hext : ∀ χ χ' : DirichletCharacter O N, (∀ x, χ.toUnitHom x = χ'.toUnitHom x) → χ = χ' := by
    intro χ χ' h
    ext x
    simpa using congrArg Units.val (h x)
  have hone : ∀ x, (1 : DirichletCharacter O N).toUnitHom x = 1 := by
    intro x
    ext
    simp
  have hord : orderOf ψ = orderOf (ψ.toUnitHom g) := by
    rw [orderOf_eq_orderOf_iff]
    intro k
    constructor
    · intro h
      rw [← hpow, h, hone]
    · intro h
      apply hext
      intro x
      obtain ⟨a, ha⟩ := hg x
      rw [hpow, hone, ha, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  have hpos : 0 < orderOf (ψ.toUnitHom g) :=
    (ψ.toUnitHom.isOfFinOrder (isOfFinOrder_of_finite g)).orderOf_pos
  have hfwd : ∀ ψ' : DirichletCharacter O N, ψ'.toUnitHom.ker = ψ.toUnitHom.ker →
      ∃ j < orderOf ψ, j.Coprime (orderOf ψ) ∧ ψ' = ψ ^ j := by
    intro ψ' h
    have hm : ∀ x, ψ'.toUnitHom x = 1 ↔ ψ.toUnitHom x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, h]
    have ho : orderOf (ψ'.toUnitHom g) = orderOf (ψ.toUnitHom g) := by
      rw [orderOf_eq_orderOf_iff]
      intro k
      rw [← map_pow, ← map_pow, hm]
    have h1 := IsPrimitiveRoot.orderOf (ψ.toUnitHom g)
    have h2 := IsPrimitiveRoot.orderOf (ψ'.toUnitHom g)
    rw [ho] at h2
    haveI : NeZero (orderOf (ψ.toUnitHom g)) := ⟨hpos.ne'⟩
    obtain ⟨j, hj, hcop, hjj⟩ := (h1.isPrimitiveRoot_iff').1 h2
    refine ⟨j, hord ▸ hj, hord ▸ hcop, hext _ _ fun x => ?_⟩
    obtain ⟨a, ha⟩ := hg x
    have h3 : ψ.toUnitHom (x / g ^ a) = 1 := by rw [map_div, map_pow, ha, div_self']
    have h4 := (hm _).2 h3
    rw [map_div, map_pow, div_eq_one] at h4
    rw [hpow, h4, ha, ← hjj, ← pow_mul, ← pow_mul, mul_comm]
  have hbwd : ∀ j : ℕ, j.Coprime (orderOf ψ) → (ψ ^ j).toUnitHom.ker = ψ.toUnitHom.ker := by
    intro j hj
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hpow]
    constructor
    · intro h
      have h2 : ψ.toUnitHom x ^ orderOf ψ = 1 := by rw [← hpow, pow_orderOf_eq_one, hone]
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one h2)
      rw [hj.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
      exact h3
    · intro h
      rw [h, one_pow]
  refine ⟨hidx.trans hord.symm, hc, fun ψ' => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨j, -, hj⟩ := hfwd ψ' h
    exact ⟨j, hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact hbwd j hj
  · have hset : {ψ' : DirichletCharacter O N | ψ'.toUnitHom.ker = ψ.toUnitHom.ker} =
        (fun j : ℕ => ψ ^ j) ''
          ((Finset.range (orderOf ψ)).filter (fun a => (orderOf ψ).Coprime a) : Finset ℕ) := by
      ext ψ'
      constructor
      · intro h
        obtain ⟨j, hj, hcop, rfl⟩ := hfwd ψ' h
        exact ⟨j, by simpa using ⟨hj, hcop.symm⟩, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
        exact hbwd j hj'.2.symm
    rw [hset, Set.InjOn.ncard_image, Set.ncard_coe_finset, Nat.totient_eq_card_coprime]
    refine pow_injOn_Iio_orderOf.mono fun j hj => ?_
    have hj' : j < orderOf ψ ∧ (orderOf ψ).Coprime j := by simpa using hj
    exact hj'.1
