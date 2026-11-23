import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1.MuBock

private theorem sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (K : Subgroup G) (hK : IsClosed (K : Set G)) (hc : commutator G ≤ K)
    (g : G) (hg : g ∉ K) :
    ∃ χ : G → AddCircle (1 : ℚ), IsLocallyConstant χ ∧ (∀ x y, χ (x * y) = χ x + χ y) ∧
      (∀ x ∈ K, χ x = 0) ∧ χ g ≠ 0 := by
  have h := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨K, hK⟩ : ClosedSubgroup G)
  have h' : K = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ K ≤ N} := h
  rw [h', Subgroup.mem_sInf] at hg
  push Not at hg
  obtain ⟨N, ⟨hNo, hKN⟩, hgN⟩ := hg
  have hcN : commutator G ≤ N := hc.trans hKN
  haveI hNn : N.Normal := Subgroup.Normal.of_commutator_le G hcN
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hcN).is_comm.comm
  letI : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hcomm }
  have hne : (Additive.ofMul (g : G ⧸ N)) ≠ 0 := by
    intro e
    exact hgN ((QuotientGroup.eq_one_iff g).1 e)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  refine ⟨fun x => c (Additive.ofMul (x : G ⧸ N)), ?_, ?_, ?_, hc⟩
  · have : IsLocallyConstant (fun x : G => (x : G ⧸ N)) :=
      (IsLocallyConstant.iff_continuous _).2 QuotientGroup.continuous_mk
    exact this.comp (fun y => c (Additive.ofMul y))
  · intro x y
    simp only [QuotientGroup.mk_mul, ofMul_mul, map_add]
  · intro x hx
    have : (x : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).2 (hKN hx)
    simp only [this, ofMul_one, map_zero]

private theorem lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G → AddCircle (1 : ℚ)) (h1 : IsLocallyConstant χ) (h2 : ∀ x y, χ (x * y) = χ x + χ y) :
    ∃ (a : G → ℚ) (c : G × G → ℤ), IsLocallyConstant a ∧ IsLocallyConstant c ∧
      (∀ g, (a g : AddCircle (1 : ℚ)) = χ g) ∧ ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h) := by
  have hs : Function.Surjective (fun x : ℚ => (x : AddCircle (1 : ℚ))) := QuotientAddGroup.mk_surjective
  choose σ hσ using hs
  have ha : IsLocallyConstant (fun g => σ (χ g)) := h1.comp σ
  refine ⟨fun g => σ (χ g), fun p => ⌊σ (χ p.1) + σ (χ p.2) - σ (χ (p.1 * p.2))⌋, ha, ?_, fun g => hσ _, ?_⟩
  · have a1 := ha.comp_continuous (continuous_fst : Continuous (Prod.fst : G × G → G))
    have a2 := ha.comp_continuous (continuous_snd : Continuous (Prod.snd : G × G → G))
    have a3 := ha.comp_continuous (continuous_mul : Continuous (fun p : G × G => p.1 * p.2))
    exact ((a1.add a2).sub a3).comp Int.floor
  · intro g h
    have e : ((σ (χ g) + σ (χ h) - σ (χ (g * h)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      have hσ' : ∀ y, ((σ y : ℚ) : AddCircle (1 : ℚ)) = y := hσ
      rw [AddCircle.coe_sub, AddCircle.coe_add, hσ', hσ', hσ', h2, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 e
    simp only [← hn, zsmul_eq_mul, mul_one, Int.floor_intCast]

private theorem divide {G : Type} [Group G] [TopologicalSpace G] (l : ℕ) [Fact l.Prime]
    (a : G → ℚ) (c : G × G → ℤ) (ha : IsLocallyConstant a)
    (hc : ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h)) (f : G → ZMod l) (hf : Continuous f)
    (hfc : ∀ g h, f h - f (g * h) + f g = (c (g, h) : ZMod l)) :
    ∃ ψ : G → AddCircle (1 : ℚ), IsLocallyConstant ψ ∧ (∀ x y, ψ (x * y) = ψ x + ψ y) ∧
      ∀ g, l • ψ g = (a g : AddCircle (1 : ℚ)) := by
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hf' : IsLocallyConstant f := (IsLocallyConstant.iff_continuous _).2 hf
  refine ⟨fun g => (((a g - ((f g).val : ℚ)) / l : ℚ) : AddCircle (1 : ℚ)),
    ha.comp₂ hf' (fun x y => (((x - (y.val : ℚ)) / l : ℚ) : AddCircle (1 : ℚ))), ?_, ?_⟩
  · intro g h
    have e : ((c (g, h) - ((f h).val - (f (g * h)).val + (f g).val : ℤ) : ℤ) : ZMod l) = 0 := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
      rw [hfc, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 e
    have hk' := congrArg (Int.cast : ℤ → ℚ) hk
    push_cast at hk'
    rw [hc] at hk'
    rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_add, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one]
    field_simp
    linear_combination -hk'
  · intro g
    rw [← sub_eq_zero, ← AddCircle.coe_nsmul, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-((f g).val : ℤ), ?_⟩
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul]
    push_cast
    field_simp
    ring

private theorem cocycle {G : Type} [Group G] [TopologicalSpace G] (l : ℕ) [Fact l.Prime]
    (a : G → ℚ) (c : G × G → ℤ) (hcl : IsLocallyConstant c)
    (hc : ∀ g h, (c (g, h) : ℚ) = a g + a h - a (g * h)) :
    (fun p => (c p : ZMod l)) ∈ Z2 (charRep (1 : G →* (ZMod l)ˣ)) := by
  refine (mem_cocycles2 _ _).2 ⟨(hcl.comp (Int.cast : ℤ → ZMod l)).continuous, fun g h k => ?_⟩
  have e : c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    have : ((c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [hc, hc, hc, hc, mul_assoc]
      ring
    exact_mod_cast this
  have e' := congrArg (Int.cast : ℤ → ZMod l) e
  push_cast at e'
  simpa [charRep_apply] using e'

private theorem add_pow' {G : Type} [Group G] (ψ : G → AddCircle (1 : ℚ))
    (h : ∀ x y, ψ (x * y) = ψ x + ψ y) (x : G) (n : ℕ) : ψ (x ^ n) = n • ψ x := by
  induction n with
  | zero =>
    have := h 1 1
    rw [mul_one] at this
    simpa using this
  | succ n ih => rw [pow_succ, h, ih, succ_nsmul]

private theorem dvd_of_smul (l : ℕ) [Fact l.Prime] (x : AddCircle (1 : ℚ)) (hx : x ≠ 0) (hl : l • x = 0)
    (i : ℤ) (hi : i • x = 0) : (i : ZMod l) = 0 := by
  have e : addOrderOf x = l := addOrderOf_eq_prime hl hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← e]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.2 hi

private theorem core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (l : ℕ) [Fact l.Prime] (C : Subgroup G) (hC : IsClosed (C : Set G))
    (hcC : commutator G ≤ C)
    (hk : ∀ ψ : G → AddCircle (1 : ℚ), IsLocallyConstant ψ → (∀ x y, ψ (x * y) = ψ x + ψ y) → ∀ x ∈ C, ψ x = 0)
    [Finite (H2 (charRep (1 : G →* (ZMod l)ˣ)))] (hcard : Nat.card (H2 (charRep (1 : G →* (ZMod l)ˣ))) ≤ l)
    (s t : G) (hs : s ^ l ∈ C) (ht : t ^ l ∈ C) (hsC : s ∉ C) : ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ C := by
  by_contra hcon
  have hp : l.Prime := Fact.out
  haveI hCn : C.Normal := Subgroup.Normal.of_commutator_le G hcC
  have hfo : IsOfFinOrder (s : G ⧸ C) := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨l, hp.pos, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hs
  haveI : IsClosed (C : Set G) := hC
  let K : Subgroup G := (Subgroup.zpowers (s : G ⧸ C)).comap (QuotientGroup.mk' C)
  have hKc : IsClosed (K : Set G) := by
    have : IsClosed (Subgroup.zpowers (s : G ⧸ C) : Set (G ⧸ C)) := (finite_zpowers.2 hfo).isClosed
    exact this.preimage QuotientGroup.continuous_mk
  have hCK : C ≤ K := fun x hx => by
    show (x : G ⧸ C) ∈ Subgroup.zpowers (s : G ⧸ C)
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hsK : s ∈ K := Subgroup.mem_zpowers (s : G ⧸ C)
  have htK : t ∉ K := fun h => by
    have h' : (t : G ⧸ C) ∈ Subgroup.zpowers (s : G ⧸ C) := h
    obtain ⟨n, hn⟩ := hfo.mem_powers_iff_mem_zpowers.2 h'
    refine hcon ⟨n, (QuotientGroup.eq_one_iff _).1 ?_⟩
    have hn' : (s : G ⧸ C) ^ n = t := hn
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hn', mul_inv_cancel]
  obtain ⟨χ₁, l1, m1, k1, n1⟩ := sep C hC hcC s hsC
  obtain ⟨χ₂, l2, m2, k2, n2⟩ := sep K hKc (hcC.trans hCK) t htK
  obtain ⟨a₁, c₁, la1, lc1, e1, r1⟩ := lift χ₁ l1 m1
  obtain ⟨a₂, c₂, la2, lc2, e2, r2⟩ := lift χ₂ l2 m2
  let z₁ : Z2 (charRep (1 : G →* (ZMod l)ˣ)) := ⟨_, cocycle l a₁ c₁ lc1 r1⟩
  let z₂ : Z2 (charRep (1 : G →* (ZMod l)ˣ)) := ⟨_, cocycle l a₂ c₂ lc2 r2⟩
  let F : ZMod l × ZMod l → H2 (charRep (1 : G →* (ZMod l)ˣ)) := fun p =>
    Submodule.Quotient.mk (p.1 • z₁ + p.2 • z₂)
  have hF : Function.Injective F := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    have h0 := (Submodule.Quotient.eq _).1 hpq
    obtain ⟨f, hf, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 (Submodule.mem_comap.1 h0)
    obtain ⟨i, hi⟩ := ZMod.intCast_surjective (p₁ - q₁)
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (p₂ - q₂)
    have hla : IsLocallyConstant (fun g => (i : ℚ) * a₁ g + (j : ℚ) * a₂ g) :=
      la1.comp₂ la2 (fun x y => (i : ℚ) * x + (j : ℚ) * y)
    obtain ⟨ψ, lψ, mψ, eψ⟩ := divide l (fun g => (i : ℚ) * a₁ g + (j : ℚ) * a₂ g)
      (fun p => i * c₁ p + j * c₂ p) hla (fun g h => by push_cast; rw [r1, r2]; ring) f hf (fun g h => by
        have := congrFun hd (g, h)
        simp [charRep_apply, z₁, z₂] at this
        push_cast
        rw [hi, hj, this]
        ring)
    have key : ∀ x, x ^ l ∈ C → i • χ₁ x + j • χ₂ x = 0 := fun x hx => by
      have h1 := hk ψ lψ mψ _ hx
      rw [add_pow' ψ mψ, eψ, AddCircle.coe_add, ← zsmul_eq_mul, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_zsmul, e1, e2] at h1
      exact h1
    have hi0 : (i : ZMod l) = 0 := by
      have h1 := key s hs
      rw [k2 s hsK, smul_zero, add_zero] at h1
      exact dvd_of_smul l _ n1 (by rw [← add_pow' χ₁ m1]; exact k1 _ hs) i h1
    have hj0 : (j : ZMod l) = 0 := by
      have h1 := key t ht
      obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hi0
      have h2 : l • χ₁ t = 0 := by rw [← add_pow' χ₁ m1]; exact k1 _ ht
      rw [hk, mul_comm, mul_smul, natCast_zsmul, h2, smul_zero, zero_add] at h1
      exact dvd_of_smul l _ n2 (by rw [← add_pow' χ₂ m2]; exact k2 _ (hCK ht)) j h1
    rw [hi0, eq_comm, sub_eq_zero] at hi
    rw [hj0, eq_comm, sub_eq_zero] at hj
    rw [hi, hj]
  have hle := (Nat.card_le_card_of_injective F hF).trans hcard
  rw [Nat.card_prod, Nat.card_zmod] at hle
  have := hp.two_le
  nlinarith

end UpperTheory.V.Ws.X1.MuBock

theorem UpperTheory.V.Ws.X1.muBock :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → Finite (H2 (charRep (1 : H →* (ZMod l)ˣ))) → Nat.card (H2 (charRep (1 : H →* (ZMod l)ˣ))) ≤ l → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) := by
  intro Γ _ _ _ _ _ _ l _ H hH hfin hcard s hs t ht hsl htl hsC
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH.isCompact
  have hmap : (commutator H).map H.subtype = ⁅H, H⁆ := Subgroup.map_subtype_commutator H
  let C : Subgroup H := (⁅H, H⁆ : Subgroup Γ).topologicalClosure.comap H.subtype
  have hC : IsClosed (C : Set H) :=
    (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hcC : commutator H ≤ C := by
    rw [← Subgroup.map_le_iff_le_comap, hmap]
    exact Subgroup.le_topologicalClosure _
  obtain ⟨n, hn⟩ := UpperTheory.V.Ws.X1.MuBock.core l C hC hcC (fun ψ h1 h2 x hx => by
    let φ : H →* Multiplicative (AddCircle (1 : ℚ)) :=
      MonoidHom.mk' (fun x => Multiplicative.ofAdd (ψ x)) (fun x y => by rw [h2, ofAdd_add])
    have hkc : IsClosed (φ.ker : Set H) := (h1.isClopen_fiber 0).isClosed
    have hkc' : IsClosed (φ.ker.map H.subtype : Set Γ) := hH.isClosedMap_subtype_val _ hkc
    have hle : (⁅H, H⁆ : Subgroup Γ) ≤ φ.ker.map H.subtype := by
      rw [← hmap]
      exact Subgroup.map_mono (Abelianization.commutator_subset_ker φ)
    obtain ⟨y, hy, e⟩ := Subgroup.topologicalClosure_minimal _ hle hkc' hx
    have e' : y = x := Subtype.ext e
    rw [← e']
    exact hy) hcard ⟨s, hs⟩ ⟨t, ht⟩ hsl htl hsC
  exact ⟨n, hn⟩
