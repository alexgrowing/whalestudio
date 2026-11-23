import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_ker_mul_card_range_eq_card {G H : Type} [AddGroup G] [AddGroup H] (f : G →+ H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem UpperTheory.V.Pa.cCount :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (c : Γ), c * c = 1 → IsUnit (2 : R) → (∀ Z : AddSubgroup (Γ → M), Finite Z → (Bl ρ).toAddSubgroup ≤ Z → (∀ z ∈ Z, ∀ g h, z (g * h) = z g + ρ g (z h)) → Nat.card Z * Nat.card {m : M // ρ c m = m} = {z | z ∈ Z ∧ z c = 0}.ncard * Nat.card M) ∧ Nat.card (Bl ρ) * Nat.card ρ.invariants = Nat.card M ∧ {z | z ∈ Bl ρ ∧ z c = 0}.ncard * Nat.card ρ.invariants = Nat.card {m : M // ρ c m = m} := by
  intro R Γ M _ _ _ _ _ ρ c hc h2
  let f : M →+ (Γ → M) :=
    { toFun := fun m g => ρ g m - m
      map_zero' := by ext g; simp
      map_add' := by intro a b; ext g; simp; abel }
  have hf : ∀ m g, f m g = ρ g m - m := fun _ _ => rfl
  have hBl : ∀ z, z ∈ Bl ρ ↔ z ∈ f.range := by
    intro z
    simp only [Bl, LinearMap.mem_range, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
  have hker : ∀ m, m ∈ f.ker ↔ m ∈ ρ.invariants := by
    intro m
    rw [AddMonoidHom.mem_ker, Representation.mem_invariants]
    constructor
    · intro h g
      have := congrFun h g
      rw [hf] at this
      simpa [sub_eq_zero] using this
    · intro h
      ext g
      simp [hf, h g]
  have cardBl : Nat.card (Bl ρ) = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hBl)
  have cardInv : Nat.card ρ.invariants = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hker m).symm))
  let d : M →+ M :=
    { toFun := fun m => ρ c m - m
      map_zero' := by simp
      map_add' := by intro a b; simp; abel }
  have hd : ∀ m, d m = ρ c m - m := fun _ => rfl
  have cardFix : Nat.card {m : M // ρ c m = m} = Nat.card d.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by
      rw [AddMonoidHom.mem_ker, hd, sub_eq_zero]))
  have hdM : Nat.card d.range * Nat.card {m : M // ρ c m = m} = Nat.card M := by
    rw [cardFix, mul_comm]
    exact card_ker_mul_card_range_eq_card d
  let Mc : AddSubgroup M :=
    { carrier := {m | ρ c m = m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        rw [map_neg, ha] }
  have cardMc : Nat.card {m : M // ρ c m = m} = Nat.card Mc :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))
  let f' : Mc →+ (Γ → M) := f.comp Mc.subtype
  have hf' : ∀ x, f' x = f x.1 := fun _ => rfl
  have cardKer' : Nat.card f'.ker = Nat.card ρ.invariants := by
    rw [cardInv]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have := AddMonoidHom.mem_ker.1 x.2
          rw [hf'] at this
          exact AddMonoidHom.mem_ker.2 this⟩
        invFun := fun v => ⟨⟨v.1, ((hker _).1 v.2 |> (Representation.mem_invariants ρ _).1) c⟩, by
          apply AddMonoidHom.mem_ker.2
          rw [hf']
          exact AddMonoidHom.mem_ker.1 v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hRange' : ∀ z, z ∈ f'.range ↔ z ∈ {z | z ∈ Bl ρ ∧ z c = 0} := by
    intro z
    simp only [Set.mem_setOf_eq, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(hBl _).2 ⟨x.1, (hf' x).symm⟩, ?_⟩
      rw [hf', hf, sub_eq_zero]
      exact x.2
    · rintro ⟨hz, hzc⟩
      obtain ⟨m, rfl⟩ := (hBl z).1 hz
      rw [hf, sub_eq_zero] at hzc
      exact ⟨⟨m, hzc⟩, rfl⟩
  have cardR' : Nat.card f'.range = {z | z ∈ Bl ρ ∧ z c = 0}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight hRange')
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ hle hcoc
    let ev : Z →+ M :=
      { toFun := fun z => z.1 c
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hev : ∀ z, ev z = z.1 c := fun _ => rfl
    have kerEv : Nat.card ev.ker = {z | z ∈ Z ∧ z c = 0}.ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, by
            have := AddMonoidHom.mem_ker.1 x.2
            rwa [hev] at this⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, AddMonoidHom.mem_ker.2 (by rw [hev]; exact y.2.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have rangeEv : ∀ x, x ∈ ev.range ↔ x ∈ d.range := by
      intro x
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        rw [hev]
        have h1 := hcoc z hz 1 1
        simp only [mul_one, map_one, Module.End.one_apply] at h1
        have hz1 : z 1 = 0 := by
          have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h1.symm
          exact add_left_cancel this
        have h2c := hcoc z hz c c
        rw [hc, hz1] at h2c
        obtain ⟨u, hu⟩ := h2
        refine ⟨-((↑u⁻¹ : R) • z c), ?_⟩
        rw [hd, map_neg, map_smul]
        have hneg : ρ c (z c) = -z c := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h2c.symm
        rw [hneg, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul]
        have : (↑u⁻¹ : R) + ↑u⁻¹ = 1 := by
          rw [← Units.inv_mul u, hu]
          ring
        rw [this, one_smul]
      · rintro ⟨m, rfl⟩
        have hmem : f m ∈ Z := hle ((Submodule.mem_toAddSubgroup _).2 ((hBl _).2 ⟨m, rfl⟩))
        refine ⟨⟨f m, hmem⟩, ?_⟩
        show f m c = d m
        rw [hf, hd]
    have cardRangeEv : Nat.card ev.range = Nat.card d.range :=
      Nat.card_congr (Equiv.subtypeEquivRight rangeEv)
    rw [← kerEv, ← card_ker_mul_card_range_eq_card ev, cardRangeEv, mul_assoc, hdM]
  · rw [cardBl, cardInv, mul_comm]
    exact card_ker_mul_card_range_eq_card f
  · rw [← cardR', ← cardKer', cardMc, mul_comm]
    exact card_ker_mul_card_range_eq_card f'
