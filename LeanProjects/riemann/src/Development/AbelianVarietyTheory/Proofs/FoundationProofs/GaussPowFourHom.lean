import Mathlib

noncomputable section

namespace GlobalTheory.TripleIntertwiner

open Classical

theorem quad_four {M G : Type*} [AddCommGroup M] [AddCommGroup G] (β : M →+ M →+ G) (a b c d : ℤ)
    (x y z w : M) :
    β (a • x - b • y - c • z - d • w) (a • x - b • y - c • z - d • w) +
      β (b • x + a • y - d • z + c • w) (b • x + a • y - d • z + c • w) +
      β (c • x + d • y + a • z - b • w) (c • x + d • y + a • z - b • w) +
      β (d • x - c • y + b • z + a • w) (d • x - c • y + b • z + a • w) =
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (β x x + β y y + β z z + β w w) := by
  simp only [map_add, map_sub, map_zsmul, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply]
  module

theorem gauss_pow_four_hom {M : Type*} [AddCommGroup M] [Fintype M] (β : M →+ M →+ Additive ℂˣ) :
    (∑ m, ((Additive.toMul (β m m) : ℂˣ) : ℂ)) ^ 4 = (∑ m, ((Additive.toMul (β m m) : ℂˣ) : ℂ)⁻¹) ^ 4 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (Fintype.card M - 1)
  have hc : 1 ≤ Fintype.card M := Fintype.card_pos
  have hz : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 = (Fintype.card M : ℤ) - 1 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub hc] at this
    exact this
  have hneg : ∀ m : M, ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • m = -m := by
    intro m
    rw [hz, sub_smul, natCast_zsmul, card_nsmul_eq_zero]; simp
  let T : M × M × M × M → M × M × M × M := fun p =>
    ((a : ℤ) • p.1 - (b : ℤ) • p.2.1 - (c : ℤ) • p.2.2.1 - (d : ℤ) • p.2.2.2,
     (b : ℤ) • p.1 + (a : ℤ) • p.2.1 - (d : ℤ) • p.2.2.1 + (c : ℤ) • p.2.2.2,
     (c : ℤ) • p.1 + (d : ℤ) • p.2.1 + (a : ℤ) • p.2.2.1 - (b : ℤ) • p.2.2.2,
     (d : ℤ) • p.1 - (c : ℤ) • p.2.1 + (b : ℤ) • p.2.2.1 + (a : ℤ) • p.2.2.2)
  let T' : M × M × M × M → M × M × M × M := fun p =>
    (-((a : ℤ) • p.1 + (b : ℤ) • p.2.1 + (c : ℤ) • p.2.2.1 + (d : ℤ) • p.2.2.2),
     -(-((b : ℤ) • p.1) + (a : ℤ) • p.2.1 + (d : ℤ) • p.2.2.1 - (c : ℤ) • p.2.2.2),
     -(-((c : ℤ) • p.1) - (d : ℤ) • p.2.1 + (a : ℤ) • p.2.2.1 + (b : ℤ) • p.2.2.2),
     -(-((d : ℤ) • p.1) + (c : ℤ) • p.2.1 - (b : ℤ) • p.2.2.1 + (a : ℤ) • p.2.2.2))
  have hT : Function.LeftInverse T' T := by
    rintro ⟨x, y, z, w⟩
    simp only [T, T', Prod.mk.injEq, neg_eq_iff_eq_neg]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hneg x]; module
    · rw [← hneg y]; module
    · rw [← hneg z]; module
    · rw [← hneg w]; module
  have hbij : Function.Bijective T := Finite.injective_iff_bijective.mp hT.injective
  let Q : M × M × M × M → Additive ℂˣ := fun p =>
    β p.1 p.1 + β p.2.1 p.2.1 + β p.2.2.1 p.2.2.1 + β p.2.2.2 p.2.2.2
  have hQ : ∀ p, Q (T p) = -Q p := by
    rintro ⟨x, y, z, w⟩
    have e : ∀ m : M, -β m m = ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) • β m m := by
      intro m
      rw [← map_zsmul, hneg, map_neg]
    refine (quad_four β a b c d x y z w).trans ?_
    simp only [Q, neg_add, e, smul_add]
  have key : ∀ g : M → ℂ, (∑ m, g m) ^ 4 =
      ∑ p : M × M × M × M, g p.1 * g p.2.1 * g p.2.2.1 * g p.2.2.2 := by
    intro g
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [key, key, ← hbij.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 := congrArg (fun t : Additive ℂˣ => ((Additive.toMul t : ℂˣ) : ℂ)) (hQ p)
  simp only [Q, toMul_add, toMul_neg, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv] at h1
  exact h1

theorem gauss_pow_four {M : Type*} [AddCommGroup M] [Fintype M] (β : M → M → ℂ)
    (hl : ∀ x x' y, β (x + x') y = β x y * β x' y) (hr : ∀ x y y', β x (y + y') = β x y * β x y')
    (hne : ∀ x y, β x y ≠ 0) :
    (∑ m, β m m) ^ 4 = (∑ m, (β m m)⁻¹) ^ 4 := by
  let γ : M →+ M →+ Additive ℂˣ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (Units.mk0 (β x y) (hne x y))) (by
      intro y y'
      rw [← ofMul_mul]; congr 1; ext; simp [hr]))
    (by
      intro x x'
      ext y
      simp [hl])
  simpa [γ] using gauss_pow_four_hom γ

section
variable {V : Type*} [AddCommGroup V]

abbrev rep {B A : AddSubgroup V} (q : A ⧸ B.addSubgroupOf A) : V := ((Quotient.out q : A) : V)

theorem rep_mem {B A : AddSubgroup V} (q : A ⧸ B.addSubgroupOf A) : rep q ∈ A := (Quotient.out q : A).2

theorem rep_mk {B A : AddSubgroup V} (a : A) :
    ∃ l, l ∈ A ∧ l ∈ B ∧ rep (QuotientAddGroup.mk a : A ⧸ B.addSubgroupOf A) = a + l := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul (B.addSubgroupOf A) a
  refine ⟨((h : A) : V), (h : A).2, h.2, ?_⟩
  unfold rep; rw [hh]; rfl

theorem rep_add {B A : AddSubgroup V} (q q' : A ⧸ B.addSubgroupOf A) :
    ∃ l, l ∈ A ∧ l ∈ B ∧ rep (q + q') = rep q + rep q' + l := by
  have := rep_mk (B := B) ((Quotient.out q : A) + Quotient.out q')
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  exact this

theorem sum_refine {F : Type} [AddCommMonoid F] {A₀ A B : AddSubgroup V} (hB : A₀ ≤ B)
    [Fintype (A ⧸ A₀.addSubgroupOf A)] [Fintype (A ⧸ B.addSubgroupOf A)] (g : V → F)
    (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ B → g (x + l) = g x) :
    ∃ k : ℕ, k * B.relIndex A = A₀.relIndex A ∧
      ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) = k • ∑ q : A ⧸ B.addSubgroupOf A, g (rep q) := by
  have hle : A₀.addSubgroupOf A ≤ B.addSubgroupOf A := AddSubgroup.comap_mono hB
  let π : A ⧸ A₀.addSubgroupOf A →+ A ⧸ B.addSubgroupOf A :=
    QuotientAddGroup.map _ _ (AddMonoidHom.id A) hle
  have hπ : ∀ a : A, π (QuotientAddGroup.mk a) = QuotientAddGroup.mk a := fun a => rfl
  have hsurj : Function.Surjective π := by
    intro q
    exact ⟨QuotientAddGroup.mk (Quotient.out q), by rw [hπ, QuotientAddGroup.out_eq']⟩
  have hfib : ∀ q, (Finset.univ.filter fun x => π x = q).card = (Finset.univ.filter fun x => π x = 0).card :=
    fun q => AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj q) ⟨0, map_zero _⟩
  have main : ∀ {G : Type} [AddCommMonoid G] (u : A ⧸ B.addSubgroupOf A → G),
      ∑ q, u (π q) = (Finset.univ.filter fun x => π x = 0).card • ∑ q, u q := by
    intro G _ u
    rw [← Finset.sum_fiberwise Finset.univ π, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => u q) (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, hfib]
  refine ⟨(Finset.univ.filter fun x => π x = 0).card, ?_, ?_⟩
  · have := main (G := ℕ) (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at this
    unfold AddSubgroup.relIndex AddSubgroup.index
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, this]
  · rw [← main (fun q => g (rep q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨l, h1, h2, h3⟩ := rep_mk (B := B) (Quotient.out q : A)
    rw [← hπ, QuotientAddGroup.out_eq'] at h3
    rw [h3, hg _ (rep_mem q) _ h1 h2]

end

section
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]

def itw (W : V → F →ₗ[ℂ] F) (A B : AddSubgroup V) (f : F) : F :=
  ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) • ∑ᶠ q : B ⧸ A.addSubgroupOf B, W (rep q) f

variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}

theorem itw_eq (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (f : F) (hf : ∀ x ∈ A, W x f = f) :
    ∃ ρ : ℂ, ρ ^ 2 * ((A₀.relIndex B : ℂ) * (A₀.relIndex (A ⊓ B) : ℂ)) = 1 ∧
      itw W A B f = ρ • ∑ q : B ⧸ A₀.addSubgroupOf B, W (rep q) f := by
  have h0 : A₀.relIndex B ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have h1 : A.relIndex B ≠ 0 := fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hA h)
  haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h1
  letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
  obtain ⟨k, hk, hs⟩ := sum_refine (A := B) hA (fun x => W x f) (fun x hx l hl hl' => by
    have := H.1 x l f
    rw [hf l hl', cB x hx l hl, one_smul] at this
    exact this.symm)
  have hk' : k = A₀.relIndex (A ⊓ B) := by
    have := AddSubgroup.relIndex_mul_relIndex A₀ (A ⊓ B) B (le_inf hA hB) inf_le_right
    rw [AddSubgroup.inf_relIndex_right, ← hk] at this
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1) this).symm
  have hk0 : (k : ℂ) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hk; exact h0 hk.symm
  have hn : (A.relIndex B : ℂ) ≠ 0 := by exact_mod_cast h1
  have hsq : ((Real.sqrt ((A.addSubgroupOf B).index : ℝ) : ℝ) : ℂ) ^ 2 = (A.relIndex B : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; rfl
  refine ⟨((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * (k : ℂ)⁻¹, ?_, ?_⟩
  · rw [← hk', ← hk, mul_pow, inv_pow, hsq]
    push_cast
    field_simp
  · rw [hs, itw, finsum_eq_sum_of_fintype, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc,
      inv_mul_cancel₀ hk0, mul_one]

theorem proj_translate (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A : AddSubgroup V}
    [Fintype (A ⧸ A₀.addSubgroupOf A)] (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f) (v : V) (hv : ∀ l ∈ A₀, c l v = 1 ∧ c v l = 1) :
    ∑ q : A ⧸ A₀.addSubgroupOf A, W (rep q) (W v f) =
      (if v ∈ A then (A₀.relIndex A : ℂ) else 0) • f := by
  split_ifs with h
  · rw [hf v h, Finset.sum_congr rfl (g := fun _ => f) (fun q _ => hf _ (rep_mem q)), Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul, ← Nat.card_eq_fintype_card]
    rfl
  · let χ : V → ℂ := fun x => c x v / c v x
    have hχ : ∀ x y, χ (x + y) = χ x * χ y := by
      intro x y; simp only [χ, H.2.1, H.2.2.1, mul_div_mul_comm]
    have hW : ∀ x ∈ A, W x (W v f) = χ x • W v f := by
      intro x hx
      have h1 := H.1 v x f
      rw [hf x hx] at h1
      rw [H.1, h1, smul_smul, add_comm]
      simp only [χ]
      rw [div_mul_cancel₀ _ (H.2.2.2 _ _)]
    obtain ⟨x₀, hx₀, hne⟩ : ∃ x ∈ A, c x v ≠ c v x := by
      by_contra hh
      push_neg at hh
      exact h (hsd v hh)
    have hp : ∀ x l, l ∈ A₀ → χ (x + l) = χ x := by
      intro x l hl
      rw [hχ]; simp only [χ]; rw [(hv l hl).1, (hv l hl).2]; simp
    have hsum : ∑ q : A ⧸ A₀.addSubgroupOf A, χ (rep q) = 0 := by
      let q₀ : A ⧸ A₀.addSubgroupOf A := QuotientAddGroup.mk ⟨x₀, hx₀⟩
      have e := Equiv.sum_comp (Equiv.addLeft q₀) (fun q => χ (rep q))
      have e2 : ∀ q, χ (rep (Equiv.addLeft q₀ q)) = χ x₀ * χ (rep q) := by
        intro q
        obtain ⟨l, -, hl, h3⟩ := rep_add q₀ q
        obtain ⟨l', -, hl', h4⟩ := rep_mk (B := A₀) (⟨x₀, hx₀⟩ : A)
        show χ (rep (q₀ + q)) = _
        rw [h3, hp _ _ hl, hχ, h4, hp _ _ hl']
      simp only [e2, ← Finset.mul_sum] at e
      have h1 : χ x₀ - 1 ≠ 0 := by
        simp only [χ]
        rw [sub_ne_zero, Ne, div_eq_one_iff_eq (H.2.2.2 _ _)]
        exact hne
      have : (χ x₀ - 1) * ∑ q : A ⧸ A₀.addSubgroupOf A, χ (rep q) = 0 := by
        rw [sub_mul, e]; ring
      exact (mul_eq_zero.mp this).resolve_left h1
    rw [Finset.sum_congr rfl (fun q _ => hW _ (rep_mem q)), ← Finset.sum_smul, hsum, zero_smul, zero_smul]

theorem proj_triple (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B C : AddSubgroup V} (hB : A₀ ≤ B) (hC : A₀ ≤ C)
    [Fintype (A ⧸ A₀.addSubgroupOf A)] [Fintype (B ⧸ A₀.addSubgroupOf B)]
    [Fintype (C ⧸ A₀.addSubgroupOf C)]
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f) :
    ∑ x : A ⧸ A₀.addSubgroupOf A, W (rep x) (∑ z : C ⧸ A₀.addSubgroupOf C, W (rep z)
      (∑ y : B ⧸ A₀.addSubgroupOf B, W (rep y) f)) =
      ((A₀.relIndex A : ℂ) * ∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) • f := by
  simp only [map_sum, H.1 (rep _ : V) (rep _ : V) f, map_smul]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.smul_sum, proj_translate H cA hsd f hf, smul_smul]
  · congr 1
    split_ifs <;> ring
  · intro l hl
    rw [H.2.1, H.2.2.1, cB _ (hB hl) _ (rep_mem y), cB _ (rep_mem y) _ (hB hl),
      cC _ (hC hl) _ (rep_mem z), cC _ (rep_mem z) _ (hC hl)]
    simp

theorem gauss_triple (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A B C : AddSubgroup V} (hA : A₀ ≤ A) (hB : A₀ ≤ B) (hC : A₀ ≤ C)
    [Fintype (B ⧸ A₀.addSubgroupOf B)] [Fintype (C ⧸ A₀.addSubgroupOf C)]
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1) :
    (∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) ^ 4 =
    (∑ y : B ⧸ A₀.addSubgroupOf B, ∑ z : C ⧸ A₀.addSubgroupOf C,
        if rep y + rep z ∈ A then c (rep y) (rep z) else 0) ^ 4 := by
  let M : AddSubgroup ((C ⧸ A₀.addSubgroupOf C) × (B ⧸ A₀.addSubgroupOf B)) :=
    AddSubgroup.map ((QuotientAddGroup.mk' _).prodMap (QuotientAddGroup.mk' _))
      (A.comap (C.subtype.coprod B.subtype))
  have hM : ∀ p, p ∈ M ↔ rep p.1 + rep p.2 ∈ A := by
    rintro ⟨z, y⟩
    constructor
    · rintro ⟨⟨z', y'⟩, h1, h2⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      obtain ⟨l, -, hl, h3⟩ := rep_mk (B := A₀) z'
      obtain ⟨l', -, hl', h4⟩ := rep_mk (B := A₀) y'
      have h1' : (z' : V) + y' ∈ A := h1
      show rep (QuotientAddGroup.mk z') + rep (QuotientAddGroup.mk y') ∈ A
      rw [h3, h4, add_add_add_comm]
      exact A.add_mem h1' (A.add_mem (hA hl) (hA hl'))
    · intro h
      exact ⟨(Quotient.out z, Quotient.out y), h, Prod.ext (QuotientAddGroup.out_eq' z)
        (QuotientAddGroup.out_eq' y)⟩
  have key := gauss_pow_four (M := M) (fun m m' => c (rep m.1.1) (rep m'.1.2))
    (fun x x' y => by
      obtain ⟨l, -, hl, h3⟩ := rep_add x.1.1 x'.1.1
      show c (rep (x.1.1 + x'.1.1)) _ = _
      rw [h3, H.2.1, H.2.1, cB _ (hB hl) _ (rep_mem _), mul_one])
    (fun x y y' => by
      obtain ⟨l, -, hl, h3⟩ := rep_add y.1.2 y'.1.2
      show c _ (rep (y.1.2 + y'.1.2)) = _
      rw [h3, H.2.2.1, H.2.2.1, cC _ (rep_mem _) _ (hC hl), mul_one])
    (fun x y => H.2.2.2 _ _)
  have conv : ∀ g : (C ⧸ A₀.addSubgroupOf C) × (B ⧸ A₀.addSubgroupOf B) → ℂ,
      ∑ m : M, g m = ∑ z, ∑ y, if rep z + rep y ∈ A then g (z, y) else 0 := by
    intro g
    rw [← Finset.sum_subtype (Finset.univ.filter fun p => rep p.1 + rep p.2 ∈ A) (p := fun p => p ∈ M)
      (by intro p; simp [hM]), Finset.sum_filter, Fintype.sum_prod_type]
  rw [conv (fun p => c (rep p.1) (rep p.2)), conv (fun p => (c (rep p.1) (rep p.2))⁻¹)] at key
  rw [key, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [add_comm (rep y)]
  split_ifs with h
  · have := cA _ h _ h
    rw [H.2.1, H.2.2.1, H.2.2.1, cB _ (rep_mem y) _ (rep_mem y), cC _ (rep_mem z) _ (rep_mem z),
      one_mul, mul_one] at this
    exact (eq_inv_of_mul_eq_one_right this).symm
  · rfl

theorem itw_triple (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A B C : AddSubgroup V}
    (fA : (A ⊓ B ⊓ C).relIndex A ≠ 0) (fB : (A ⊓ B ⊓ C).relIndex B ≠ 0) (fC : (A ⊓ B ⊓ C).relIndex C ≠ 0)
    (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1) (cB : ∀ x ∈ B, ∀ y ∈ B, c x y = 1)
    (cC : ∀ x ∈ C, ∀ y ∈ C, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f)
    (h1 : ∀ x ∈ B, W x (itw W A B f) = itw W A B f)
    (h2 : ∀ x ∈ C, W x (itw W B C (itw W A B f)) = itw W B C (itw W A B f))
    (h3 : ∀ x ∈ C, W x (itw W A C f) = itw W A C f)
    (h4 : ∀ x ∈ B, W x (itw W C B (itw W A C f)) = itw W C B (itw W A C f)) :
    ∃ μ μ' : ℂ, μ ^ 4 = μ' ^ 4 ∧ itw W C A (itw W B C (itw W A B f)) = μ • f ∧
      itw W B A (itw W C B (itw W A C f)) = μ' • f := by
  set A₀ := A ⊓ B ⊓ C with hA₀
  have hA : A₀ ≤ A := inf_le_left.trans inf_le_left
  have hB : A₀ ≤ B := inf_le_left.trans inf_le_right
  have hC : A₀ ≤ C := inf_le_right
  haveI : Finite (A ⧸ A₀.addSubgroupOf A) := Nat.finite_of_card_ne_zero fA
  haveI : Finite (B ⧸ A₀.addSubgroupOf B) := Nat.finite_of_card_ne_zero fB
  haveI : Finite (C ⧸ A₀.addSubgroupOf C) := Nat.finite_of_card_ne_zero fC
  letI : Fintype (A ⧸ A₀.addSubgroupOf A) := Fintype.ofFinite _
  letI : Fintype (B ⧸ A₀.addSubgroupOf B) := Fintype.ofFinite _
  letI : Fintype (C ⧸ A₀.addSubgroupOf C) := Fintype.ofFinite _
  obtain ⟨r1, s1, e1⟩ := itw_eq H hA hB cB f hf
  obtain ⟨r2, s2, e2⟩ := itw_eq H hB hC cC _ h1
  obtain ⟨r3, s3, e3⟩ := itw_eq H hC hA cA _ h2
  obtain ⟨r4, s4, e4⟩ := itw_eq H hA hC cC f hf
  obtain ⟨r5, s5, e5⟩ := itw_eq H hC hB cB _ h3
  obtain ⟨r6, s6, e6⟩ := itw_eq H hB hA cA _ h4
  have t1 := proj_triple H hB hC cA cB cC hsd f hf
  have t2 := proj_triple H hC hB cA cC cB hsd f hf
  have g := gauss_triple H hA hB hC cA cB cC
  generalize (∑ z : C ⧸ A₀.addSubgroupOf C, ∑ y : B ⧸ A₀.addSubgroupOf B,
        if rep z + rep y ∈ A then c (rep z) (rep y) else 0) = S at t1 g
  generalize (∑ y : B ⧸ A₀.addSubgroupOf B, ∑ z : C ⧸ A₀.addSubgroupOf C,
        if rep y + rep z ∈ A then c (rep y) (rep z) else 0) = S' at t2 g
  refine ⟨r3 * r2 * r1 * ((A₀.relIndex A : ℂ) * S), r6 * r5 * r4 * ((A₀.relIndex A : ℂ) * S'), ?_, ?_, ?_⟩
  rotate_left
  · rw [e3, e2, e1]
    simp only [map_smul, ← Finset.smul_sum]
    rw [t1, smul_smul, smul_smul, smul_smul]
  · rw [e6, e5, e4]
    simp only [map_smul, ← Finset.smul_sum]
    rw [t2, smul_smul, smul_smul, smul_smul]
  · rw [inf_comm C A] at s3
    rw [inf_comm C B] at s5
    rw [inf_comm B A] at s6
    have hr : (r3 * r2 * r1) ^ 2 = (r6 * r5 * r4) ^ 2 := by
      set a := (A₀.relIndex A : ℂ)
      set b := (A₀.relIndex B : ℂ)
      set d := (A₀.relIndex C : ℂ)
      set ab := (A₀.relIndex (A ⊓ B) : ℂ)
      set ac := (A₀.relIndex (A ⊓ C) : ℂ)
      set bc := (A₀.relIndex (B ⊓ C) : ℂ)
      have p1 : (r3 * r2 * r1) ^ 2 * (a * b * d * ab * ac * bc) = 1 := by
        calc _ = (r1 ^ 2 * (b * ab)) * (r2 ^ 2 * (d * bc)) * (r3 ^ 2 * (a * ac)) := by ring
          _ = 1 := by rw [s1, s2, s3]; ring
      have p2 : (r6 * r5 * r4) ^ 2 * (a * b * d * ab * ac * bc) = 1 := by
        calc _ = (r4 ^ 2 * (d * ac)) * (r5 ^ 2 * (b * bc)) * (r6 ^ 2 * (a * ab)) := by ring
          _ = 1 := by rw [s4, s5, s6]; ring
      rw [eq_inv_of_mul_eq_one_left p1, eq_inv_of_mul_eq_one_left p2]
    have hr4 : (r3 * r2 * r1) ^ 4 = (r6 * r5 * r4) ^ 4 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, pow_mul, hr]
    rw [mul_pow, mul_pow (r6 * r5 * r4), hr4, mul_pow (A₀.relIndex A : ℂ), mul_pow (A₀.relIndex A : ℂ), g]

end

end GlobalTheory.TripleIntertwiner
