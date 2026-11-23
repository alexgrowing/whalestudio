import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt

noncomputable section

open scoped Classical
open MulAction

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

section SlopeTestRemainingChoices

variable {T : Type} [Group T]

private abbrev omk (T : Type) [Group T] {Z : Type} [MulAction T Z] (z : Z) : orbitRel.Quotient T Z :=
  Quotient.mk (orbitRel T Z) z

private lemma omk_eq_iff {Z : Type} [MulAction T Z] (a b : Z) :
    omk T a = omk T b ↔ ∃ t : T, t • b = a := by
  constructor
  · intro h
    have h' : orbitRel T Z a b := Quotient.exact h
    rw [orbitRel_apply] at h'
    exact h'
  · intro h
    apply Quotient.sound
    show orbitRel T Z a b
    rw [orbitRel_apply]
    exact h

private lemma exists_smul_out {Z : Type} [MulAction T Z] (z : Z) :
    ∃ t : T, t • z = Quotient.out (omk T z) :=
  (omk_eq_iff _ _).1 (Quotient.out_eq (omk T z))

private lemma inv_out {Z α : Type} [MulAction T Z] (f : Z → α) (hf : ∀ (t : T) z, f (t • z) = f z) (z : Z) :
    f (Quotient.out (omk T z)) = f z := by
  obtain ⟨t, ht⟩ := exists_smul_out (T := T) z
  rw [← ht, hf]

private lemma relIndex_stab_smul {Z : Type} [MulAction T Z] (C : Subgroup T) [hC : C.Normal] (t : T) (z : Z) :
    (stabilizer T (t • z)).relIndex C = (stabilizer T z).relIndex C := by
  have hmap : C.map (MulAut.conj t).toMonoidHom = C := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hC.conj_mem b hb t
    · intro ha
      refine ⟨t⁻¹ * a * t, ?_, ?_⟩
      · simpa using hC.conj_mem a ha t⁻¹
      · simp [MulAut.conj_apply, mul_assoc]
  have h := Subgroup.relIndex_map_map_of_injective (stabilizer T z) C
    (f := (MulAut.conj t).toMonoidHom) (MulAut.conj t).injective
  rw [hmap] at h
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact h

private lemma stab_pair_le {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y : Y) :
    stabilizer T ((x, y) : X × Y) ≤ stabilizer T x := by
  intro t ht
  rw [mem_stabilizer_iff] at ht ⊢
  exact congrArg Prod.fst ht

private lemma stab_swap {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y : Y) :
    stabilizer T ((y, x) : Y × X) = stabilizer T ((x, y) : X × Y) := by
  ext t
  simp only [mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
  exact and_comm

private lemma card_fiber {X Y : Type} [MulAction T X] [MulAction T Y] (x : X) (y0 : Y) (S : Finset Y)
    (hS : ∀ y, omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y) → y ∈ S) :
    (S.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y)).card =
      (stabilizer T ((x, y0) : X × Y)).relIndex (stabilizer T x) := by
  have h1 := index_stabilizer (stabilizer T x) y0
  have h2 : stabilizer (stabilizer T x) y0 = (stabilizer T ((x, y0) : X × Y)).subgroupOf (stabilizer T x) := by
    ext ⟨h, hh⟩
    rw [mem_stabilizer_iff] at hh
    simp only [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Prod.smul_mk, Prod.mk.injEq, hh, true_and]
    rfl
  have h3 : orbit (stabilizer T x) y0 =
      ((S.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y) : Finset Y) : Set Y) := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h, hh0⟩, rfl⟩
      have hh : h • x = x := mem_stabilizer_iff.1 hh0
      have e : omk T ((x, (⟨h, hh0⟩ : stabilizer T x) • y0) : X × Y) = omk T ((x, y0) : X × Y) :=
        (omk_eq_iff _ _).2 ⟨h, by simp [hh]⟩
      exact ⟨hS _ e, e⟩
    · rintro ⟨-, e⟩
      obtain ⟨t, ht⟩ := (omk_eq_iff _ _).1 e
      simp only [Prod.smul_mk, Prod.mk.injEq] at ht
      exact ⟨⟨t, mem_stabilizer_iff.2 ht.1⟩, ht.2⟩
  rw [Subgroup.relIndex, ← h2, h1, h3, Set.ncard_coe_finset]

private lemma one_side {X Y : Type} [MulAction T X] [MulAction T Y] (C : Subgroup T) [C.Normal]
    (hX : ∀ x : X, stabilizer T x ≤ C) (F : X → Y → ℂ)
    (hF : ∀ (t : T) x y, F (t • x) (t • y) = F x y) (hfin : ∀ x, {y | F x y ≠ 0}.Finite)
    (hP : {p : orbitRel.Quotient T (X × Y) | F (Quotient.out p).1 (Quotient.out p).2 ≠ 0}.Finite) :
    ∑ᶠ q : orbitRel.Quotient T X,
        (((stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) * ∑ᶠ y, F (Quotient.out q) y =
      ∑ᶠ p : orbitRel.Quotient T (X × Y),
        (((stabilizer T (Quotient.out p)).relIndex C : ℕ) : ℂ) * F (Quotient.out p).1 (Quotient.out p).2 := by
  have hFp : ∀ z : X × Y, F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 = F z.1 z.2 :=
    inv_out (fun z : X × Y => F z.1 z.2) (fun t z => hF t z.1 z.2)
  have hGp : ∀ z : X × Y, (((stabilizer T (Quotient.out (omk T z))).relIndex C : ℕ) : ℂ) *
      F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 =
      (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2 :=
    inv_out (fun z : X × Y => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2)
      (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF])
  let π : orbitRel.Quotient T (X × Y) → orbitRel.Quotient T X := fun p => omk T (Quotient.out p).1
  have hπ : ∀ z : X × Y, π (omk T z) = omk T z.1 :=
    inv_out (fun z : X × Y => omk T z.1) (fun t z => (omk_eq_iff _ _).2 ⟨t, rfl⟩)
  have hRHS := finsum_eq_sum_of_support_subset (s := hP.toFinset)
    (fun p : orbitRel.Quotient T (X × Y) => (((stabilizer T (Quotient.out p)).relIndex C : ℕ) : ℂ) *
      F (Quotient.out p).1 (Quotient.out p).2) (by
      intro p hp
      simp only [Function.mem_support] at hp
      simpa using right_ne_zero_of_mul hp)
  have hLHS := finsum_eq_sum_of_support_subset (s := hP.toFinset.image π)
    (fun q : orbitRel.Quotient T X => (((stabilizer T (Quotient.out q)).relIndex C : ℕ) : ℂ) *
      ∑ᶠ y, F (Quotient.out q) y) (by
      intro q hq
      simp only [Function.mem_support] at hq
      have hs := right_ne_zero_of_mul hq
      have : ∃ y, F (Quotient.out q) y ≠ 0 := by
        by_contra hno
        push_neg at hno
        exact hs (by simp [hno])
      obtain ⟨y, hy⟩ := this
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨omk T ((Quotient.out q, y) : X × Y), ?_, ?_⟩
      · rw [hFp]; exact hy
      · rw [hπ]; exact Quotient.out_eq q)
  rw [hLHS, hRHS, ← Finset.sum_fiberwise_of_maps_to (s := hP.toFinset) (t := hP.toFinset.image π) (g := π)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  refine Finset.sum_congr rfl fun q _ => ?_
  set x := Quotient.out q with hxdef
  have hq : omk T x = q := Quotient.out_eq q
  have h1 : ∑ᶠ y, F x y = ∑ y ∈ (hfin x).toFinset, F x y :=
    finsum_eq_sum_of_support_subset _ (by intro y hy; simpa using hy)
  rw [h1, Finset.mul_sum]
  have maps : ∀ y ∈ (hfin x).toFinset, omk T ((x, y) : X × Y) ∈ hP.toFinset.filter fun p => π p = q := by
    intro y hy
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy ⊢
    refine ⟨?_, ?_⟩
    · rw [hFp]; exact hy
    · rw [hπ]; exact hq
  rw [← Finset.sum_fiberwise_of_maps_to maps]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
  obtain ⟨hpP, hpq⟩ := hp
  obtain ⟨t, ht⟩ : ∃ t : T, t • (Quotient.out p).1 = x := (omk_eq_iff _ _).1 (hq.trans hpq.symm)
  have hp0 : omk T ((x, t • (Quotient.out p).2) : X × Y) = p := by
    refine Eq.trans ((omk_eq_iff _ _).2 ⟨t, ?_⟩) (Quotient.out_eq p)
    exact Prod.ext ht rfl
  obtain ⟨y0, hy0⟩ : ∃ y0, omk T ((x, y0) : X × Y) = p := ⟨_, hp0⟩
  subst hy0
  have hne : F x y0 ≠ 0 := by
    have := hpP
    rw [hFp] at this
    exact this
  have hconst : ∀ y ∈ (hfin x).toFinset.filter fun y => omk T ((x, y) : X × Y) = omk T ((x, y0) : X × Y),
      (((stabilizer T x).relIndex C : ℕ) : ℂ) * F x y = (((stabilizer T x).relIndex C : ℕ) : ℂ) * F x y0 := by
    intro y hy
    obtain ⟨s, hs⟩ := (omk_eq_iff _ _).1 (Finset.mem_filter.1 hy).2
    simp only [Prod.smul_mk, Prod.mk.injEq] at hs
    have := hF s x y0
    rw [hs.1, hs.2] at this
    rw [this]
  have hcard := card_fiber (T := T) x y0 (hfin x).toFinset (by
    intro y hy
    obtain ⟨s, hs⟩ := (omk_eq_iff _ _).1 hy
    simp only [Prod.smul_mk, Prod.mk.injEq] at hs
    have := hF s x y0
    rw [hs.1, hs.2] at this
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [this]
    exact hne)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, hGp, nsmul_eq_mul,
    ← Subgroup.relIndex_mul_relIndex _ _ _ (stab_pair_le x y0) (hX x)]
  push_cast
  ring

end SlopeTestRemainingChoices

theorem orbFub : OrbFub := by
  intro T X Y _ _ _ C _ hX hY F hF hx hy hq
  have hFp : ∀ z : X × Y, F (Quotient.out (omk T z)).1 (Quotient.out (omk T z)).2 = F z.1 z.2 :=
    inv_out (fun z : X × Y => F z.1 z.2) (fun t z => hF t z.1 z.2)
  have hFp' : ∀ z : Y × X, F (Quotient.out (omk T z)).2 (Quotient.out (omk T z)).1 = F z.2 z.1 :=
    inv_out (fun z : Y × X => F z.2 z.1) (fun t z => hF t z.2 z.1)
  have hP : {p : orbitRel.Quotient T (X × Y) | F (Quotient.out p).1 (Quotient.out p).2 ≠ 0}.Finite := by
    refine (hq.biUnion fun q _ => (hx (Quotient.out q)).image
      (fun y => omk T ((Quotient.out q, y) : X × Y))).subset ?_
    intro p hp
    obtain ⟨t, ht⟩ := exists_smul_out (T := T) (Quotient.out p).1
    have hne : F (Quotient.out (omk T (Quotient.out p).1)) (t • (Quotient.out p).2) ≠ 0 := by
      rw [← ht, hF]; exact hp
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop]
    refine ⟨omk T (Quotient.out p).1, ⟨_, hne⟩, _, hne, ?_⟩
    exact Eq.trans ((omk_eq_iff _ _).2 ⟨t, Prod.ext ht rfl⟩) (Quotient.out_eq p)
  let e : orbitRel.Quotient T (X × Y) ≃ orbitRel.Quotient T (Y × X) :=
    Quotient.congr (Equiv.prodComm X Y) (by
      intro a b
      show orbitRel T _ a b ↔ orbitRel T _ (Equiv.prodComm X Y a) (Equiv.prodComm X Y b)
      rw [orbitRel_apply, orbitRel_apply]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, rfl⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (Equiv.prodComm X Y).injective ht⟩)
  have he : ∀ z : X × Y, e (omk T z) = omk T (z.2, z.1) := fun z => rfl
  have hP' : {p : orbitRel.Quotient T (Y × X) | F (Quotient.out p).2 (Quotient.out p).1 ≠ 0}.Finite := by
    refine (hP.image e).subset ?_
    intro p hp
    obtain ⟨⟨y, x⟩, rfl⟩ := Quotient.exists_rep p
    refine ⟨omk T ((x, y) : X × Y), ?_, rfl⟩
    have h1 : F x y ≠ 0 := by
      have := hFp' (y, x)
      simp only at this
      rw [← this]
      exact hp
    show F (Quotient.out (omk T ((x, y) : X × Y))).1 (Quotient.out (omk T ((x, y) : X × Y))).2 ≠ 0
    rw [hFp]
    exact h1
  rw [one_side C hX F hF hx hP, one_side C hY (fun y x => F x y) (fun t y x => hF t x y) hy hP']
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun p => ?_
  obtain ⟨⟨x, y⟩, rfl⟩ := Quotient.exists_rep p
  have h1 := inv_out (T := T) (fun z : X × Y => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.1 z.2)
    (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF]) (x, y)
  have h2 := inv_out (T := T) (fun z : Y × X => (((stabilizer T z).relIndex C : ℕ) : ℂ) * F z.2 z.1)
    (fun t z => by rw [relIndex_stab_smul]; simp only [Prod.smul_fst, Prod.smul_snd, hF]) (y, x)
  refine (h1.trans ?_).trans h2.symm
  simp only
  rw [stab_swap x y]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
