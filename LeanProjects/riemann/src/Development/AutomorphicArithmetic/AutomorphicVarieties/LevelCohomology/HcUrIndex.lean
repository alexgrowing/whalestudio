import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private theorem urIndex_mem {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (J : Subgroup D) (f : Z1 ρ) :
    (Submodule.Quotient.mk f : H1 ρ) ∈ H1ur ρ J ↔ ∃ m, ∀ j ∈ J, f.1 j = ρ j m - m := by
  have hJc : Continuous J.subtype := continuous_subtype_val
  show resH1 ρ J.subtype hJc (Submodule.Quotient.mk f) = 0 ↔ _
  unfold resH1
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 ρ J.subtype hJc f : Z1 (ρ.comp J.subtype)) : J → M) ∈ B1 (ρ.comp J.subtype) ↔ _
  rw [mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have h := hm ⟨j, hj⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc] at h
    simpa using h
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j => ?_⟩
    rw [restrictCocycles1_apply ρ J.subtype hJc]
    simpa using hm j j.2

private theorem urIndex_avg {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (N : Subgroup Γ) (hN : (N.index : k) ≠ 0) (c : Γ → M)
    (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (h0 : ∀ n ∈ N, c n = 0) :
    ∃ m, ∀ g, c g = ρ g m - m := by
  classical
  have hNi : N.index ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  haveI : N.FiniteIndex := ⟨hNi⟩
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  have hconst : ∀ g n, n ∈ N → c (g * n) = c g := fun g n hn => by
    rw [hc, h0 n hn, map_zero, add_zero]
  let c' : Γ ⧸ N → M := Quotient.lift (s := QuotientGroup.leftRel N) c (fun a b hab => by
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h := hconst a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at h
    exact h.symm)
  have hc' : ∀ (h : Γ) (x : Γ ⧸ N), c' (h • x) = c h + ρ h (c' x) := by
    intro h x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    show c (h * g) = c h + ρ h (c g)
    exact hc h g
  let S := ∑ x : Γ ⧸ N, c' x
  have hS : ∀ h, S = Fintype.card (Γ ⧸ N) • c h + ρ h S := by
    intro h
    calc S = ∑ x, c' (h • x) := (Equiv.sum_comp (MulAction.toPerm h) c').symm
      _ = ∑ x, (c h + ρ h (c' x)) := Finset.sum_congr rfl fun x _ => hc' h x
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
  have hcard : (Fintype.card (Γ ⧸ N) : k) = N.index := by
    rw [Fintype.card_eq_nat_card]
    rfl
  refine ⟨-((N.index : k)⁻¹ • S), fun g => ?_⟩
  have h1 := hS g
  have h2 : S - ρ g S = (N.index : k) • c g := by
    rw [← hcard, Nat.cast_smul_eq_nsmul]
    nth_rewrite 1 [h1]
    rw [add_sub_cancel_right]
  rw [map_neg, map_smul, neg_sub_neg, ← smul_sub, h2, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem UpperTheory.V.X.urIndex :
    ∀ (l : ℕ) [Fact l.Prime] {k D M : Type} [Field k] [CharP k l] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I N : Subgroup D), N ≤ I → ¬ l ∣ N.relIndex I → H1ur ρ N = H1ur ρ I := by
  intro l _ k D M _ _ _ _ _ _ _ _ ρ hρ I N hNI hl
  ext c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.comap (Z1 ρ).subtype (B1 ρ)) c
  refine (urIndex_mem ρ N f).trans (Iff.trans ?_ (urIndex_mem ρ I f).symm)
  constructor
  · rintro ⟨m, hm⟩
    have hf := ((mem_Z1_iff_cocycle ρ _).1 f.2).2
    let cI : I → M := fun j => f.1 j - (ρ j m - m)
    have hcI : ∀ g h : I, cI (g * h) = cI g + (ρ.comp I.subtype) g (cI h) := by
      intro g h
      simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul, hf, map_mul,
        Module.End.mul_apply, map_sub]
      abel
    have h0 : ∀ n ∈ N.subgroupOf I, cI n = 0 := fun n hn => by
      simp only [cI]
      rw [hm n (Subgroup.mem_subgroupOf.1 hn), sub_self]
    have hidx : ((N.subgroupOf I).index : k) ≠ 0 := by
      have e : (N.subgroupOf I).index = N.relIndex I := rfl
      rw [e]
      intro h
      exact hl ((CharP.cast_eq_zero_iff k l _).1 h)
    obtain ⟨m', hm'⟩ := urIndex_avg (ρ.comp I.subtype) (N.subgroupOf I) hidx cI hcI h0
    refine ⟨m + m', fun j hj => ?_⟩
    have h := hm' ⟨j, hj⟩
    simp only [cI, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, map_add]
    abel
  · rintro ⟨m, hm⟩
    exact ⟨m, fun j hj => hm j (hNI hj)⟩
