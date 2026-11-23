import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors

open UpperTheory.V.FW

private theorem card_hom_surj (l : ℕ) {G A : Type} [Group G] [Group A] (π : G →* A) (hπ : Function.Surjective π)
    (P : G → Prop) (hP : ∀ u, P u ↔ π u = 1) :
    Nat.card {φ : G → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u, P u → φ u = 0} =
      Nat.card (A →* Multiplicative (ZMod l)) := by
  have key : ∀ (φ : G → ZMod l), (∀ a b, φ (a * b) = φ a + φ b) → (∀ u, P u → φ u = 0) →
      ∀ x y, π x = π y → φ x = φ y := by
    intro φ hadd hker x y hxy
    have h0 : φ (y⁻¹ * x) = 0 := hker _ ((hP _).mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel]))
    calc φ x = φ (y * (y⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = φ y := by rw [hadd, h0, add_zero]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun f => ⟨fun g => Multiplicative.toAdd (f (π g)), ?_, ?_⟩) ⟨?_, ?_⟩
  · intro a b
    simp [map_mul]
  · intro u hu
    show Multiplicative.toAdd (f (π u)) = 0
    rw [(hP u).mp hu, map_one, toAdd_one]
  · intro f f' h
    ext a
    obtain ⟨g, rfl⟩ := hπ a
    have := congrArg (fun φ => φ.1 g) h
    simpa using this
  · rintro ⟨φ, hadd, hker⟩
    refine ⟨{ toFun := fun a => Multiplicative.ofAdd (φ (Function.surjInv hπ a)), map_one' := ?_, map_mul' := ?_ }, ?_⟩
    · show Multiplicative.ofAdd (φ (Function.surjInv hπ 1)) = 1
      rw [key φ hadd hker _ 1 (by rw [Function.surjInv_eq hπ, map_one]), hker 1 ((hP 1).mpr (map_one π)), ofAdd_zero]
    · intro a b
      show Multiplicative.ofAdd (φ (Function.surjInv hπ (a * b))) =
        Multiplicative.ofAdd (φ (Function.surjInv hπ a)) * Multiplicative.ofAdd (φ (Function.surjInv hπ b))
      have e : φ (Function.surjInv hπ (a * b)) = φ (Function.surjInv hπ a * Function.surjInv hπ b) :=
        key φ hadd hker _ _ (by simp only [map_mul, Function.surjInv_eq hπ])
      rw [e, hadd, ofAdd_add]
    · apply Subtype.ext
      funext g
      show Multiplicative.toAdd (Multiplicative.ofAdd (φ (Function.surjInv hπ (π g)))) = φ g
      rw [toAdd_ofAdd]
      exact key φ hadd hker _ _ (Function.surjInv_eq hπ _)

private theorem card_hom_sub_le (l : ℕ) [Fact l.Prime] (A : Type) [CommGroup A] [Finite A] (B : Subgroup A) :
    Nat.card (B →* Multiplicative (ZMod l)) ≤ Nat.card (A →* Multiplicative (ZMod l)) := by
  rw [(cardTors B).2 l, (cardTors A).2 l, (cardTors B).1 l, (cardTors A).1 l]
  refine Nat.card_le_card_of_injective (fun x => ⟨((x : B) : A), ?_⟩) ?_
  · have hx := x.2
    rw [MonoidHom.mem_ker] at hx ⊢
    simp only [powMonoidHom_apply] at hx ⊢
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h

theorem UpperTheory.V.FW.homCyc :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U N : Subgroup Γ) [U.Normal] [N.Normal] [N.FiniteIndex], N ≤ U → IsCyclic (Γ ⧸ U) → (∀ g, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ N) → Nat.card {φ : U → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u : U, u.1 ∈ N → φ u = 0} ≤ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ N, φ u = 0} := by
  intro l _ Γ _ U N _ _ _ hNU hcyc hcomm
  have hU : ∀ (h : Γ ⧸ N) (u : Γ), u ∈ U → Commute h (u : Γ ⧸ N) := by
    intro h u hu
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
    have := hcomm g u hu
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨gU, hgen⟩ := IsCyclic.exists_generator (α := Γ ⧸ U)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective gU
  have hdecomp : ∀ x : Γ, ∃ i : ℤ, ∃ u ∈ U, x = g0 ^ i * u := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen (x : Γ ⧸ U))
    refine ⟨i, (g0 ^ i)⁻¹ * x, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [← QuotientGroup.mk_zpow] at hi
    exact QuotientGroup.eq.mp hi
  have hcomm' : ∀ a b : Γ ⧸ N, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨i, u1, hu1, rfl⟩ := hdecomp x
    obtain ⟨j, u2, hu2, rfl⟩ := hdecomp y
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
    have c12 : Commute ((g0 : Γ ⧸ N) ^ i) ((g0 : Γ ⧸ N) ^ j) := Commute.zpow_zpow_self _ _ _
    apply Commute.eq
    exact Commute.mul_left (c12.mul_right (hU _ u2 hu2))
      (((hU _ u1 hu1).symm).mul_right (hU _ u2 hu2))
  letI : CommGroup (Γ ⧸ N) := { (inferInstance : Group (Γ ⧸ N)) with mul_comm := hcomm' }
  let f : U →* Γ ⧸ N := (QuotientGroup.mk' N).comp U.subtype
  have h1 := card_hom_surj l f.rangeRestrict f.rangeRestrict_surjective (fun u : U => u.1 ∈ N) (by
    intro u
    rw [← Subtype.coe_inj]
    simp [f, QuotientGroup.eq_one_iff])
  have h2 := card_hom_surj l (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (fun u => u ∈ N)
    (by intro u; simp [QuotientGroup.eq_one_iff])
  beta_reduce at h1 h2
  rw [h1, h2]
  exact card_hom_sub_le l (Γ ⧸ N) f.range
