import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem comm_of_integral {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hk : (p : k) = 0) (f g : k →+* k)
    {x : k} (hx : IsIntegral ℤ x) : f (g x) = g (f x) := by
  haveI hchar : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hk
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxi : IsIntegral (ZMod p) x := hx.tower_top
  haveI := Algebra.finite_adjoin_simple_of_isIntegral hxi
  haveI hF : Finite (Algebra.adjoin (ZMod p) {x}) := Module.finite_of_finite (ZMod p)
  have hxmem : x ∈ Algebra.adjoin (ZMod p) {x} := Algebra.subset_adjoin (Set.mem_singleton x)
  have hfin : (Set.range (fun n : ℕ => x ^ n)).Finite := by
    refine Set.Finite.subset (s := ((Algebra.adjoin (ZMod p) {x} : Subalgebra (ZMod p) k) : Set k))
      (Set.finite_coe_iff.mp hF) ?_
    rintro _ ⟨n, rfl⟩
    exact Subalgebra.pow_mem _ hxmem n
  have hni : ¬ Function.Injective (fun n : ℕ => x ^ n) := fun hinj =>
    (Set.infinite_range_of_injective hinj) hfin
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, j, heq', hij⟩ := hni
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ x ^ N = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have h2 : x ^ i * x ^ (j - i) = x ^ i * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
    · refine ⟨i - j, by omega, ?_⟩
      have h2 : x ^ j * x ^ (i - j) = x ^ j * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
  haveI : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity N k)
  have mem : ∀ y : k, y ^ N = 1 → ∃ a : ℤ, y = ((ζ : kˣ) : k) ^ a := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hN0.ne'] at hy
      exact zero_ne_one hy
    have hu : Units.mk0 y hy0 ∈ rootsOfUnity N k := by
      rw [mem_rootsOfUnity]
      ext
      simp [hy]
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨_, hu⟩)
    refine ⟨a, ?_⟩
    have h3 := congrArg (fun u : rootsOfUnity N k => ((u : kˣ) : k)) ha
    simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h3
    exact h3.symm
  have hzN : ((ζ : kˣ) : k) ^ N = 1 := by
    have h1 : (ζ : kˣ) ^ N = 1 := (mem_rootsOfUnity _ _).mp ζ.2
    have h2 := congrArg Units.val h1
    simpa using h2
  obtain ⟨a, ha⟩ := mem (f ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨b, hb⟩ := mem (g ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨c, hc⟩ := mem x hN
  rw [hc]
  simp only [map_zpow₀, ha, hb]
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private def resA {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨σ x, (apply_mem_iff_of_mem_Dec hσ _).2 x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : Ω) b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ (a : Ω) b)

private theorem resA_local {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : IsLocalHom (resA hσ) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have h1 : A.valuation (a : Ω) < 1 := (A.valuation_lt_one_iff a).1 h
  have h2 : A.valuation (σ a) < 1 := (valuation_apply_lt_one_iff hσ _).2 h1
  exact (A.valuation_lt_one_iff (resA hσ a)).2 h2 ha

private theorem comm_mem_Ine {p : ℕ} (hp : p.Prime) (hA : A.valuation (p : Ω) < 1) {g h : G ℚ Ω}
    (hg : g ∈ Dec (F := ℚ) A) (hh : h ∈ Dec (F := ℚ) A) : g * h * g⁻¹ * h⁻¹ ∈ Ine (F := ℚ) A := by
  haveI := resA_local hg
  haveI := resA_local hh
  have hkp : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  have hint : ∀ z : Ω, IsIntegral ℤ z → ∀ hz : z ∈ A,
      IsIntegral ℤ (IsLocalRing.residue A ⟨z, hz⟩) := by
    intro z hz hzA
    have h1 : IsIntegral ℤ (⟨z, hzA⟩ : A) := by
      rw [← isIntegral_algHom_iff (A.toSubring.subtype.toIntAlgHom) Subtype.val_injective]
      exact hz
    exact h1.map_of_comp_eq (RingHom.id ℤ) (IsLocalRing.residue A) (RingHom.ext_int _ _)
  have comm : ∀ w : A,
      IsLocalRing.ResidueField.map (resA hg) (IsLocalRing.ResidueField.map (resA hh)
        (IsLocalRing.residue A w)) =
      IsLocalRing.ResidueField.map (resA hh) (IsLocalRing.ResidueField.map (resA hg)
        (IsLocalRing.residue A w)) := by
    intro w
    obtain ⟨s, t, hs, ht, hvs, hst⟩ := exists_den ℚ A (A.valuation_le_one w)
    have hsA := mem_of_isIntegral_int A hs
    have htA := mem_of_isIntegral_int A ht
    have hsunit : IsLocalRing.residue A ⟨s, hsA⟩ ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simp [hvs]
    have hw : IsLocalRing.residue A w
        = IsLocalRing.residue A ⟨t, htA⟩ / IsLocalRing.residue A ⟨s, hsA⟩ := by
      rw [eq_div_iff hsunit, ← map_mul]
      congr 1
      apply Subtype.ext
      show (w : Ω) * s = t
      rw [mul_comm]
      exact hst
    rw [hw, map_div₀, map_div₀, map_div₀, map_div₀,
      comm_of_integral hp hkp _ _ (hint t ht htA), comm_of_integral hp hkp _ _ (hint s hs hsA)]
  have key : ∀ y : Ω, y ∈ A → A.valuation (g (h y) - h (g y)) < 1 := by
    intro y hy
    have c := comm ⟨y, hy⟩
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue] at c
    have c2 : IsLocalRing.residue A
        (resA hg (resA hh ⟨y, hy⟩) - resA hh (resA hg ⟨y, hy⟩)) = 0 := by
      rw [map_sub, c, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at c2
    exact c2
  have hDec : g * h * g⁻¹ * h⁻¹ ∈ Dec (F := ℚ) A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ hh)
  show _ ∈ Inertia (F := ℚ) A
  simp only [Inertia, Set.mem_setOf_eq]
  refine ⟨hDec, fun x hx => ?_⟩
  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
  have hyA : g⁻¹ (h⁻¹ x) ∈ A :=
    (apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hg) _).2
      ((apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hh) _).2 hxA)
  have e : (g * h * g⁻¹ * h⁻¹) x - x = g (h (g⁻¹ (h⁻¹ x))) - h (g (g⁻¹ (h⁻¹ x))) := by
    simp only [AlgEquiv.mul_apply]
    congr 1
    rw [← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply,
      ← AlgEquiv.mul_apply h h⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
  rw [e]
  exact key _ hyA

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.abP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ p ∈ D.Sb, (∃ τ ∈ D.Ip p, D.ψ τ ≠ 1 ∧ ∀ s ∈ D.Ip p, ∃ n : ℕ, D.ψ s = D.ψ τ ^ n) ∧ ∀ g ∈ D.Gp p, ∀ h ∈ D.Gp p, g * h * g⁻¹ * h⁻¹ ∈ D.Ip p ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D hD p hp
  unfold Raw.Sb at hp
  obtain ⟨hpS, hpl, hldvd⟩ := Finset.mem_filter.mp hp
  have hpp : p.Prime := hD.S_prime p hpS
  have hv := hD.pl_over p hpp
  refine ⟨?_, ?_⟩
  · haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
    haveI : Finite D.ψ.range :=
      Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange D.ψ).toEquiv
    haveI hfin : Finite (Subgroup.map D.ψ (D.Ip p)) :=
      Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range D.ψ _))
        (Subgroup.inclusion_injective _)
    haveI : IsCyclic (Subgroup.map D.ψ (D.Ip p)) := subgroup_units_cyclic _
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Subgroup.map D.ψ (D.Ip p))
    obtain ⟨τ, hτI, hτγ⟩ := Subgroup.mem_map.mp γ.2
    refine ⟨τ, hτI, ?_, ?_⟩
    · intro h1
      have hγ1 : γ = 1 := Subtype.ext (by rw [← hτγ, h1]; rfl)
      have hsub : ∀ x : Subgroup.map D.ψ (D.Ip p), x = 1 := by
        intro x
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hγ x)
        rw [← hz, hγ1, one_zpow]
      have hcard : Nat.card (Subgroup.map D.ψ (D.Ip p)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
      rw [hcard] at hldvd
      exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp hldvd)
    · intro s hs
      have hsH : (⟨D.ψ s, Subgroup.mem_map_of_mem _ hs⟩ : Subgroup.map D.ψ (D.Ip p))
          ∈ Submonoid.powers γ := mem_powers_iff_mem_zpowers.2 (hγ _)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hsH
      refine ⟨n, ?_⟩
      have h2 := congrArg Subtype.val hn
      simp only [SubgroupClass.coe_pow] at h2
      rw [hτγ]
      exact h2.symm
  · intro g hg h hh
    refine ⟨comm_mem_Ine hpp hv hg hh, ?_⟩
    show g * h * g⁻¹ * h⁻¹ ∈ D.ψ.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (D.ψ g), mul_assoc (D.ψ h), mul_inv_cancel, mul_one, mul_inv_cancel]
