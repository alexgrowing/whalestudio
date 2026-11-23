import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProdMap

open UpperTheory.V.AlgebraTools UpperTheory.V.AlgebraTools.Cx

theorem UpperTheory.V.AlgebraTools.zhatFin :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Type) [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul A M] (ρ : Representation A G M) [CompactSpace G] [Finite M] [DiscreteTopology M] (I : Subgroup G) [I.Normal] (φ : G), ContAct ρ →
      Dense ((I ⊔ Subgroup.zpowers φ : Subgroup G) : Set G) →
      (∀ k : ℕ, 0 < k → ∃ χ : G →* Multiplicative (ZMod k), IsOpen (χ.ker : Set G) ∧ I ≤ χ.ker ∧ χ φ = Multiplicative.ofAdd 1) →
      ∀ m, (∀ u ∈ I, ρ u m = m) → ∃! z : crossed ρ, (∀ u ∈ I, z.1 u = 0) ∧ z.1 φ = m := by
  intro A _ G _ _ _ M _ _ _ _ _ ρ _ _ _ I hI φ hρ hd hχ m hm
  have hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by rw [map_mul]; rfl
  have hinv : ∀ g x, ρ g⁻¹ (ρ g x) = x := fun g x => by rw [← hmul, inv_mul_cancel, map_one]; rfl
  have hinv' : ∀ g x, ρ g (ρ g⁻¹ x) = x := fun g x => by rw [← hmul, mul_inv_cancel, map_one]; rfl
  have hall : ∀ S : Subgroup G, IsClosed (S : Set G) → I ≤ S → φ ∈ S → ∀ g, g ∈ S := by
    intro S hS h1 h2 g
    have h3 : I ⊔ Subgroup.zpowers φ ≤ S := sup_le h1 ((Subgroup.zpowers_le).2 h2)
    exact hS.closure_subset_iff.2 (show ((I ⊔ Subgroup.zpowers φ : Subgroup G) : Set G) ⊆ S from h3) (hd g)
  apply existsUnique_of_exists_of_unique
  · let T : Equiv.Perm M :=
      { toFun := fun x => m + ρ φ x
        invFun := fun x => ρ φ⁻¹ (x - m)
        left_inv := fun x => by simp only [add_sub_cancel_left, hinv]
        right_inv := fun x => by simp only [hinv', add_sub_cancel] }
    have hT : ∀ x, T x = m + ρ φ x := fun _ => rfl
    have hk : 0 < orderOf T := orderOf_pos T
    obtain ⟨χ, hχo, hχI, hχφ⟩ := hχ (orderOf T) hk
    haveI : NeZero (orderOf T) := ⟨hk.ne'⟩
    let Θ : G → Equiv.Perm M := fun g => T ^ (Multiplicative.toAdd (χ g)).val
    have hΘmul : ∀ g h x, Θ (g * h) x = Θ g (Θ h x) := fun g h x => by
      have : Θ (g * h) = Θ g * Θ h := by
        simp only [Θ, map_mul, toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add]
      rw [this]; rfl
    have hΘI : ∀ u ∈ I, ∀ x, Θ u x = x := fun u hu x => by
      have : χ u = 1 := hχI hu
      simp [Θ, this]
    have hΘφ : ∀ x, Θ φ x = m + ρ φ x := fun x => by
      have : Θ φ = T := by
        have e : (1 : ZMod (orderOf T)) = ((1 : ℕ) : ZMod (orderOf T)) := Nat.cast_one.symm
        simp only [Θ, hχφ, toAdd_ofAdd]
        rw [e, ZMod.val_natCast, pow_mod_orderOf, pow_one]
      rw [this, hT]
    have hlc : IsLocallyConstant χ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have ho : IsOpen {h : G | g⁻¹ * h ∈ χ.ker} := hχo.preimage (continuous_const.mul continuous_id)
      filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ χ.ker by simp)] with h hh
      have : χ (g⁻¹ * h) = 1 := hh
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have hΘc : ∀ x, Continuous fun g => Θ g x := fun x =>
      (hlc.comp fun a => (T ^ (Multiplicative.toAdd a).val) x).continuous
    have hTF : ∀ (n : ℕ) x, (∀ u ∈ I, ρ u x = x) → ∀ u ∈ I, ρ u ((T ^ n) x) = (T ^ n) x := by
      intro n x hx
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        intro u hu
        rw [pow_succ', Equiv.Perm.mul_apply, hT, map_add, hm u hu, ← hmul]
        have : u * φ = φ * (φ⁻¹ * u * φ⁻¹⁻¹) := by group
        rw [this, hmul, ih _ (hI.conj_mem u hu φ⁻¹)]
    have hΘF : ∀ g x, (∀ u ∈ I, ρ u x = x) → ∀ u ∈ I, ρ u (Θ g x) = Θ g x := fun g x hx => hTF _ x hx
    have h0 : ∀ u ∈ I, ρ u (0 : M) = 0 := fun u _ => map_zero _
    let S : Subgroup G :=
      { carrier := {g | ∀ x, (∀ u ∈ I, ρ u x = x) → Θ g x = Θ g 0 + ρ g x}
        one_mem' := fun x _ => by simp [hΘI 1 I.one_mem]
        mul_mem' := fun {g h} hg hh x hx => by
          rw [hΘmul, hΘmul, hg _ (hΘF h x hx), hg _ (hΘF h 0 h0), hh x hx, map_add, hmul, add_assoc]
        inv_mem' := fun {g} hg x hx => by
          have e1 := hg _ (hΘF g⁻¹ x hx)
          have e2 := hg _ (hΘF g⁻¹ 0 h0)
          rw [← hΘmul, mul_inv_cancel, hΘI 1 I.one_mem] at e1 e2
          have e3 : x = ρ g (Θ g⁻¹ x - Θ g⁻¹ 0) := by
            rw [map_sub, eq_sub_iff_add_eq, ← add_right_inj (Θ g 0), ← e1, add_left_comm, ← e2, add_zero]
          have e4 := congrArg (ρ g⁻¹) e3
          rw [hinv] at e4
          rw [e4, add_sub_cancel] }
    have hSc : IsClosed (S : Set G) := by
      have : (S : Set G) = ⋂ x, ⋂ _ : (∀ u ∈ I, ρ u x = x), {g | Θ g x = Θ g 0 + ρ g x} := by
        ext g; simp only [Set.mem_iInter]; rfl
      rw [this]
      refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq (hΘc x) ((hΘc 0).add ?_)
      exact Continuous.comp hρ (continuous_id.prodMk continuous_const)
    have hS := hall S hSc (fun u hu x hx => by rw [hΘI u hu, hΘI u hu, hx u hu, zero_add])
      (fun x _ => by rw [hΘφ, hΘφ, map_zero, add_zero])
    refine ⟨⟨fun g => Θ g 0, hΘc 0, fun g h => ?_⟩, fun u hu => hΘI u hu 0, ?_⟩
    · show Θ (g * h) 0 = Θ g 0 + ρ g (Θ h 0)
      rw [hΘmul]
      exact hS g _ (hΘF h 0 h0)
    · show Θ φ 0 = m
      rw [hΘφ, map_zero, add_zero]
  · rintro ⟨y, hyc, hy⟩ ⟨z, hzc, hz⟩ ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    simp only at hy1 hy2 hz1 hz2
    let S : Subgroup G :=
      { carrier := {g | y g = z g}
        one_mem' := (hy1 1 I.one_mem).trans (hz1 1 I.one_mem).symm
        mul_mem' := fun {g h} (hg : y g = z g) (hh : y h = z h) => by
          show y (g * h) = z (g * h)
          rw [hy, hz, hg, hh]
        inv_mem' := fun {g} (hg : y g = z g) => by
          show y g⁻¹ = z g⁻¹
          have e1 := hy g⁻¹ g
          have e2 := hz g⁻¹ g
          rw [inv_mul_cancel] at e1 e2
          rw [hy1 1 I.one_mem, hg] at e1
          rw [hz1 1 I.one_mem] at e2
          exact add_right_cancel (e1.symm.trans e2) }
    have hS := hall S (isClosed_eq hyc hzc) (fun u hu => (hy1 u hu).trans (hz1 u hu).symm) (hy2.trans hz2.symm)
    exact Subtype.ext (funext hS)
