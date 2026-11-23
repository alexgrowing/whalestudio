import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem cont_lev {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Γ : Type} [TopologicalSpace Γ]
    (a : O) (ha : a ≠ 0) (z : Γ → O) (hz : Alg.AdicCont (maximalIdeal O) z) :
    Continuous fun g => Lev.mk a (z g) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hle : ∀ x, x ∈ maximalIdeal O ^ n → a ∣ x := by
    intro x hx
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    rw [hu, Units.mul_left_dvd]
    exact hx
  have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hz n)
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_).continuous
  filter_upwards [hlc x] with y hy
  rw [Ideal.Quotient.eq] at hy
  rw [← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]
  exact hle _ hy

private theorem lev_kill {O : Type} [CommRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (a : O) (B : ℕ)
    (hf : Finite (H1 (scalRep (Lev a) θ))) (hB : Nat.card (H1 (scalRep (Lev a) θ)) ≤ B) (z : Γ → O) (hz : Coc θ z)
    (hc : Continuous fun g => Lev.mk a (z g)) :
    ∃ m : O, ∀ g, a ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := by
  set ρ := scalRep (Lev a) θ with hρ
  have hρg : ∀ g (x : Lev a), ρ g x = (θ g : O) • x := fun _ _ => rfl
  have hmem : (fun g => Lev.mk a (z g)) ∈ Z1 ρ := by
    rw [mem_Z1_iff_cocycle]
    refine ⟨hc, fun g h => ?_⟩
    rw [hz, hρg, map_add, ← smul_eq_mul, map_smul]
  let ζ : Z1 ρ := ⟨_, hmem⟩
  let q : H1 ρ := Submodule.Quotient.mk ζ
  have hpos : 0 < Nat.card (H1 ρ) := Nat.card_pos
  have hq : B.factorial • q = 0 := by
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hB
    rw [hk, mul_comm, mul_nsmul, card_nsmul_eq_zero']
  have hq2 : (Submodule.Quotient.mk (B.factorial • ζ) : H1 ρ) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hq
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hq2
  obtain ⟨mb, hmb⟩ := (mem_coboundaries1 ρ _).1 hq2
  obtain ⟨m, rfl⟩ := Lev.mk_surjective a mb
  refine ⟨m, fun g => ?_⟩
  rw [← Lev.mk_eq_zero]
  have := hmb g
  simp only [Submodule.subtype_apply, Submodule.coe_smul_of_tower, Pi.smul_apply] at this
  rw [map_sub, map_sub, ← nsmul_eq_mul, map_nsmul, this, hρg, ← smul_eq_mul, map_smul, sub_self]

theorem UpperTheory.V.X.So.cobLim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (θ : Γ →* Oˣ) (p : O) (B : ℕ), p ≠ 0 → p ∈ maximalIdeal O → (∃ g, θ g ≠ 1) → (∀ r : ℕ, Finite (H1 (scalRep (Lev (p ^ r)) θ)) ∧ Nat.card (H1 (scalRep (Lev (p ^ r)) θ)) ≤ B) → ∀ z : Γ → O, Coc θ z → Alg.AdicCont (maximalIdeal O) z → CobOn θ z ⊤ := by
  intro O _ _ _ _ Γ _ _ θ p B hp0 hpm hθ hfin z hz hcont
  obtain ⟨g0, hg0⟩ := hθ
  have hcl : ∀ r : ℕ, ∃ m : O, ∀ g, p ^ r ∣ (B.factorial : O) * z g - ((θ g : O) * m - m) := fun r =>
    lev_kill θ (p ^ r) B (hfin r).1 (hfin r).2 z hz (cont_lev (p ^ r) (pow_ne_zero r hp0) z hcont)
  have hpu : ¬IsUnit p := (IsLocalRing.mem_maximalIdeal p).1 hpm
  have hkey : ∀ g, ((θ g0 : O) - 1) * ((B.factorial : O) * z g) = ((θ g : O) - 1) * ((B.factorial : O) * z g0) := by
    intro g
    by_contra hne
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpu (sub_ne_zero.2 hne)
    apply hn
    obtain ⟨m, hm⟩ := hcl (n + 1)
    have e : ((θ g0 : O) - 1) * ((B.factorial : O) * z g) - ((θ g : O) - 1) * ((B.factorial : O) * z g0)
        = ((θ g0 : O) - 1) * ((B.factorial : O) * z g - ((θ g : O) * m - m))
          - ((θ g : O) - 1) * ((B.factorial : O) * z g0 - ((θ g0 : O) * m - m)) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (hm g) _) (dvd_mul_of_dvd_right (hm g0) _)
  refine ⟨((θ g0 : O) - 1) * (B.factorial : O), ?_, (B.factorial : O) * z g0, ?_⟩
  · refine mul_ne_zero (sub_ne_zero.2 fun h => hg0 (Units.val_eq_one.1 h)) ?_
    exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero B)
  · intro g _
    rw [mul_assoc, hkey g]
    ring
