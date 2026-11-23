import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Pl :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Kv :
    {F : Type} → [inst : Field F] → [NumberField F] → UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F → Type :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.cv :
    {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) → F →+* UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦ Algebra.algebraMap F (UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v)

section aux

open IsDedekindDomain NumberField Module
open scoped WithZero

namespace UpperTheory.Reformulated.B.NormIndexQuadratic

private lemma index_two {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] :
    (nsmulAddMonoidHom (α := M) 2).range.index
      = 2 ^ finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  set T : Submodule ℤ M := Submodule.torsion ℤ M with hT
  set D := (nsmulAddMonoidHom (α := M) 2).range with hD
  have hTfin : Finite T := Module.finite_of_fg_torsion T (Submodule.torsion_isTorsion)
  have h1 : D ⊔ T.toAddSubgroup =
      ((nsmulAddMonoidHom (α := M ⧸ T) 2).range).comap T.mkQ.toAddMonoidHom := by
    ext x
    simp only [AddSubgroup.mem_sup, AddSubgroup.mem_comap, AddMonoidHom.mem_range, hD]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, z, hz, rfl⟩
      refine ⟨T.mkQ y, ?_⟩
      have : T.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero T).2 hz
      simp only [nsmulAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, map_add, map_nsmul, this,
        add_zero]
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := T.mkQ_surjective y
      refine ⟨_, ⟨y, rfl⟩, x - 2 • y, ?_, by simp⟩
      have : T.mkQ (x - 2 • y) = 0 := by
        simp only [nsmulAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at hy
        rw [map_sub, map_nsmul, hy, sub_self]
      exact (Submodule.Quotient.mk_eq_zero T).1 this
  have h2 : (D ⊔ T.toAddSubgroup).index = 2 ^ finrank ℤ M := by
    rw [h1, AddSubgroup.index_comap_of_surjective _ T.mkQ_surjective,
      AddSubgroup.index_range_nsmul, finrank_quotient_eq_of_le_torsion le_rfl]
  have h3 : D.addSubgroupOf T.toAddSubgroup
      = (nsmulAddMonoidHom (α := T.toAddSubgroup) 2).range := by
    ext ⟨x, hx⟩
    simp only [AddSubgroup.mem_addSubgroupOf, hD, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨⟨a, ha⟩, h⟩ := hx
      refine ⟨⟨y, ⟨⟨a * 2, mul_mem ha (mem_nonZeroDivisors_of_ne_zero two_ne_zero)⟩, ?_⟩⟩, rfl⟩
      show (a * 2) • y = 0
      rw [mul_smul, ofNat_smul_eq_nsmul]
      exact h
    · rintro ⟨y, h⟩
      exact ⟨y, congrArg Subtype.val h⟩
  have h4 : Nat.card (nsmulAddMonoidHom (α := T.toAddSubgroup) 2).ker
      = Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩,
      fun x => ⟨⟨x.1, ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩⟩, Subtype.ext x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
    show (2 : ℤ) • x.1 = 0
    rw [ofNat_smul_eq_nsmul]
    exact x.2
  have : Finite T.toAddSubgroup := hTfin
  rw [← AddSubgroup.relIndex_mul_index (le_sup_left : D ≤ D ⊔ T.toAddSubgroup), h2,
    AddSubgroup.relIndex_sup_left, AddSubgroup.relIndex, h3, AddSubgroup.index_range, h4, mul_comm]

private lemma index_sq {K : Type*} [Field K] [CharZero K] (H : Subgroup Kˣ) (h : -1 ∈ H)
    [Module.Finite ℤ (Additive H)] :
    (powMonoidHom (α := H) 2).range.index = 2 ^ (finrank ℤ (Additive H) + 1) := by
  have h1 := index_two (M := Additive H)
  have h2 : (nsmulAddMonoidHom (α := Additive H) 2).range
      = (powMonoidHom (α := H) 2).range.toAddSubgroup := by
    ext x; rfl
  have h3 : Nat.card (nsmulAddMonoidHom (α := Additive H) 2).ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨0, ⟨Additive.ofMul ⟨-1, h⟩, ?_⟩, ?_, ?_⟩
    · show (⟨-1, h⟩ : H) ^ 2 = 1
      ext; simp
    · intro h0
      have : (1 : K) = -1 := by
        simpa using congrArg (fun x => ((Additive.toMul x.1 : H) : Kˣ).val) h0
      norm_num at this
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      have h5 : ((Additive.toMul x : H) : Kˣ).val ^ 2 = 1 := by
        have : (Additive.toMul x : H) ^ 2 = 1 := hx
        simpa using congrArg (fun x : H => (x : Kˣ).val) this
      rcases sq_eq_one_iff.1 h5 with h6 | h6
      · exact Or.inl (Subtype.ext (Subtype.ext (Units.ext h6)))
      · exact Or.inr (Subtype.ext (Subtype.ext (Units.ext h6)))
  rw [h2, Subgroup.index_toAddSubgroup, h3] at h1
  rw [h1, pow_succ]

private lemma relIndex_le_card {G α : Type*} [Group G] [Finite α] (H B : Subgroup G) (g : B → α)
    (hg : ∀ x y, g x = g y → (x : G)⁻¹ * y ∈ H) :
    H.relIndex B ≠ 0 ∧ H.relIndex B ≤ Nat.card α := by
  have hi : Function.Injective (fun q : B ⧸ H.subgroupOf B => g q.out) := by
    intro p q hpq
    rw [← p.out_eq, ← q.out_eq]
    exact Quotient.sound (QuotientGroup.leftRel_apply.2 (hg _ _ hpq))
  have : Finite (B ⧸ H.subgroupOf B) := Finite.of_injective _ hi
  exact ⟨Nat.card_pos.ne', Nat.card_le_card_of_injective _ hi⟩

private lemma pow_le_relIndex {G ι : Type*} [CommGroup G] (L : ι → Subgroup G) (H : Subgroup G)
    (I : Finset ι) (hx : ∀ i ∈ I, ∃ x ∈ H, x ∉ L i ∧ ∀ j ∈ I, j ≠ i → x ∈ L j)
    (h0 : (⨅ i ∈ I, L i).relIndex H ≠ 0) : 2 ^ I.card ≤ (⨅ i ∈ I, L i).relIndex H := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.iInf_insert] at h0 ⊢
    rw [← Subgroup.relIndex_inf_mul_relIndex] at h0 ⊢
    rw [Finset.card_insert_of_notMem ha, pow_succ, mul_comm]
    refine Nat.mul_le_mul ?_ (ih ?_ (right_ne_zero_of_mul h0))
    · obtain ⟨x, hH, hxa, hj⟩ := hx a (Finset.mem_insert_self _ _)
      have h1 := left_ne_zero_of_mul h0
      have h2 : (L a).relIndex ((⨅ i ∈ I, L i) ⊓ H) ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        refine hxa (hle ⟨?_, hH⟩)
        refine Subgroup.mem_iInf.2 fun j => Subgroup.mem_iInf.2 fun hjI => ?_
        exact hj j (Finset.mem_insert_of_mem hjI) (fun h => ha (h ▸ hjI))
      omega
    · intro i hi
      obtain ⟨x, hH, hxa, hj⟩ := hx i (Finset.mem_insert_of_mem hi)
      exact ⟨x, hH, hxa, fun j hjI => hj j (Finset.mem_insert_of_mem hjI)⟩

private lemma relIndex_le_card' {G α : Type*} [Group G] [Finite α] (H B : Subgroup G)
    (R : G → α → Prop) (h1 : ∀ x ∈ B, ∃ a, R x a)
    (h2 : ∀ x ∈ B, ∀ y ∈ B, ∀ a, R x a → R y a → x⁻¹ * y ∈ H) :
    H.relIndex B ≠ 0 ∧ H.relIndex B ≤ Nat.card α := by
  choose g hg using h1
  exact relIndex_le_card H B (fun x => g x x.2)
    (fun x y h => h2 _ x.2 _ y.2 _ (hg x x.2) (by rw [show g x x.2 = g y y.2 from h]; exact hg y y.2))

private lemma index_sup_range {G : Type*} [CommGroup G] (N : Subgroup G) (φ : G →* G)
    (h0 : N.index ≠ 0) (h : N ≤ N.comap φ) :
    (N ⊔ φ.range).index = N.relIndex (N.comap φ) := by
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ φ.range)
  have h2 := Subgroup.relIndex_mul_index h
  rw [Subgroup.relIndex_sup_left, ← Subgroup.index_comap] at h1
  have h3 : (N.comap φ).index ≠ 0 := fun h3 => h0 (by rw [← h2, h3, mul_zero])
  exact mul_left_cancel₀ h3 (by rw [h1, mul_comm, h2])

section loc
variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

private lemma v_nat (n : ℕ) : v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => push_cast; exact v.map_add_le ih (by simp)

private lemma v_two : v (2 : K) ≤ 1 := by simpa using v_nat v 2

private lemma v_four_eq : v (4 : K) = v 2 ^ 2 := by
  rw [← map_pow]; norm_num

private lemma v_four : v (4 : K) ≤ 1 := by simpa using v_nat v 4

private lemma v_eq_one {x : K} (h : v (x - 1) < 1) : v x = 1 := by
  have := v.map_one_add_of_lt h
  simpa using this

private lemma v_eq_of {x y : K} (h : v (x - y) < v y) : v x = v y := by
  have := v.map_add_eq_of_lt_left h
  simpa using this

private lemma sq_cancel {x r : ℤᵐ⁰} (hr : r ≠ 0) (h : IsSquare (x * r ^ 2)) : IsSquare x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c / r, ?_⟩
  field_simp
  rw [hc, sq]

private lemma not_sq_exp : ¬ IsSquare (WithZero.exp (-1 : ℤ)) := by
  rintro ⟨c, hc⟩
  have h0 : c ≠ 0 := by rintro rfl; simp at hc
  have := congrArg WithZero.log hc
  rw [WithZero.log_mul h0 h0, WithZero.log_exp] at this
  omega

variable [CharZero K]

private lemma v_two_ne : v (2 : K) ≠ 0 := by simp
private lemma v_four_ne : v (4 : K) ≠ 0 := by simp

private def near (c : K) (h0 : c ≠ 0) (h1 : v c ≤ 1) : Subgroup Kˣ where
  carrier := {x | v ((x : K) - 1) < v c}
  one_mem' := by simpa [zero_lt_iff] using h0
  mul_mem' := by
    intro a b ha hb
    have h : ((a * b : Kˣ) : K) - 1 = a * (b - 1) + (a - 1) := by push_cast; ring
    simp only [Set.mem_setOf_eq] at *
    rw [h]
    refine v.map_add_lt ?_ ha
    rwa [map_mul, v_eq_one v (ha.trans_le h1), one_mul]
  inv_mem' := by
    intro a ha
    have h : ((a⁻¹ : Kˣ) : K) - 1 = - ((a : K)⁻¹ * (a - 1)) := by push_cast; field_simp; ring
    simp only [Set.mem_setOf_eq] at *
    rwa [h, v.map_neg, map_mul, map_inv₀, v_eq_one v (ha.trans_le h1), inv_one, one_mul]

private def near2 : Subgroup Kˣ := near v 2 two_ne_zero (v_two v)
private def near4 : Subgroup Kˣ := near v 4 (by norm_num) (v_four v)

private lemma mem_near4 {x : Kˣ} : x ∈ near4 v ↔ v ((x : K) - 1) < v 4 := Iff.rfl

private def Qv : Subgroup Kˣ := near4 v ⊔ (powMonoidHom 2).range

private lemma mem_Qv {x : Kˣ} : x ∈ Qv v ↔ ∃ z ∈ near4 v, ∃ y : Kˣ, x = z * y ^ 2 := by
  rw [Qv, Subgroup.mem_sup]
  constructor
  · rintro ⟨z, hz, _, ⟨y, rfl⟩, rfl⟩
    exact ⟨z, hz, y, rfl⟩
  · rintro ⟨z, hz, y, rfl⟩
    exact ⟨z, hz, _, ⟨y, rfl⟩, rfl⟩

private lemma sq_mem_Qv (y : Kˣ) : y ^ 2 ∈ Qv v := (mem_Qv v).2 ⟨1, one_mem _, y, by simp⟩

private lemma mem_Qv_of {x : Kˣ} {y : K} (hx : v x = 1) (h : v (x - y ^ 2) < v 4) : x ∈ Qv v := by
  have h1 : v (y ^ 2) = 1 := by
    rw [← hx]
    refine v_eq_of v ?_
    rw [v.map_sub_swap, hx]
    exact h.trans_le (v_four v)
  have h0 : y ≠ 0 := by rintro rfl; simp at h1
  refine (mem_Qv v).2 ⟨x / (Units.mk0 y h0) ^ 2, ?_, Units.mk0 y h0, by simp⟩
  rw [mem_near4]
  have : ((x / (Units.mk0 y h0) ^ 2 : Kˣ) : K) - 1 = (x - y ^ 2) / y ^ 2 := by
    simp; field_simp
  rwa [this, map_div₀, h1, div_one]

omit [CharZero K] in
private def Nm (θ : K) : Subgroup Kˣ where
  carrier := {x | ∃ a b : K, (x : K) = a ^ 2 - θ * b ^ 2}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, b, h⟩ ⟨c, d, h'⟩
    exact ⟨a * c + θ * b * d, a * d + b * c, by push_cast; rw [h, h']; ring⟩
  inv_mem' := by
    rintro x ⟨a, b, h⟩
    refine ⟨a / x, b / x, ?_⟩
    have := x.ne_zero
    push_cast
    field_simp
    exact h

private def LN (θ : K) : Subgroup Kˣ := Nm θ ⊔ near4 v

private lemma Qv_le_LN (θ : K) : Qv v ≤ LN v θ := by
  refine sup_le le_sup_right ?_
  rintro _ ⟨y, rfl⟩
  exact Subgroup.mem_sup_left ⟨y, 0, by simp⟩

private lemma mem_LN {θ : K} {x : Kˣ} (h : x ∈ LN v θ) :
    ∃ z a b : K, v (z - 1) < v 4 ∧ x * z = a ^ 2 - θ * b ^ 2 := by
  obtain ⟨n, ⟨a, b, hn⟩, z, hz, rfl⟩ := Subgroup.mem_sup.1 h
  exact ⟨((z⁻¹ : Kˣ) : K), a, b, inv_mem hz, by rw [← hn]; simp⟩

private def Irr (ρ : K) : Prop := v ρ ≤ 1 ∧ ∀ X : K, v X ≤ 1 → v (X ^ 2 + X - ρ) = 1

omit [CharZero K] in
private lemma Irr.perturb {ρ ρ' : K} (h : Irr v ρ) (h' : v (ρ' - ρ) < 1) : Irr v ρ' := by
  refine ⟨?_, fun X hX => ?_⟩
  · have := v.map_add_le h'.le h.1
    simpa using this
  · rw [← h.2 X hX]
    refine v_eq_of v ?_
    rw [h.2 X hX, v.map_sub_swap]
    convert h' using 2
    ring

omit [CharZero K] in
private lemma Irr.aux {ρ : K} (h : Irr v ρ) (X : K) :
    ∃ r, r ≠ 0 ∧ v (X ^ 2 + X - ρ) = r ^ 2 := by
  by_cases hX : v X ≤ 1
  · exact ⟨1, one_ne_zero, by simp [h.2 X hX]⟩
  · push Not at hX
    have h0 : v X ≠ 0 := (zero_lt_one.trans hX).ne'
    refine ⟨v X, h0, ?_⟩
    rw [← map_pow]
    refine v_eq_of v ?_
    have h1 : v X < v (X ^ 2) := by
      rw [map_pow, sq]
      exact lt_mul_of_one_lt_left (zero_lt_one.trans hX) hX
    have : X ^ 2 + X - ρ - X ^ 2 = X - ρ := by ring
    rw [this]
    exact v.map_sub_lt h1 (h.1.trans_lt (hX.trans h1))

private lemma Irr.aux2 {ρ : K} (h : Irr v ρ) (x : K) :
    ∃ r, r ≠ 0 ∧ v (x ^ 2 - (1 + 4 * ρ)) = r ^ 2 := by
  obtain ⟨r, hr, h1⟩ := h.aux v ((x - 1) / 2)
  refine ⟨v 2 * r, mul_ne_zero (v_two_ne v) hr, ?_⟩
  rw [mul_pow, ← h1, ← map_pow, ← map_mul]
  congr 1
  ring

private lemma Irr.isSquare {ρ : K} (h : Irr v ρ) (x y : K) :
    IsSquare (v (x ^ 2 - (1 + 4 * ρ) * y ^ 2)) := by
  by_cases hy : y = 0
  · subst hy
    exact ⟨v x, by simp [sq]⟩
  · obtain ⟨r, -, h1⟩ := h.aux2 v (x / y)
    refine ⟨r * v y, ?_⟩
    rw [← sq, mul_pow, ← h1, ← map_pow, ← map_mul]
    congr 1
    field_simp

private lemma Irr.unit {ρ : K} (h : Irr v ρ) : v (1 + 4 * ρ) = 1 := by
  rcases (v_two v).eq_or_lt with h2 | h2
  · have := h.2 (-1 / 2) (by simp [h2])
    have h3 : (1 + 4 * ρ) = - (2 ^ 2 * ((-1 / 2) ^ 2 + -1 / 2 - ρ)) := by ring
    rw [h3, v.map_neg, map_mul, this, map_pow, h2]
    simp
  · refine v.map_one_add_of_lt ?_
    rw [map_mul, v_four_eq]
    calc v 2 ^ 2 * v ρ ≤ v 2 ^ 2 * 1 := by gcongr; exact h.1
      _ < 1 := by rw [mul_one]; exact pow_lt_one₀ zero_le h2 two_ne_zero

private lemma nonnorm_odd {ρ θ : K} (h : Irr v ρ) (hθ : ¬ IsSquare (v θ)) :
    ∃ α : Kˣ, α ∉ LN v θ := by
  have hu := h.unit v
  have h0 : 1 + 4 * ρ ≠ 0 := by intro h; simp [h] at hu
  refine ⟨Units.mk0 _ h0, fun hm => ?_⟩
  obtain ⟨z, a, b, hz, hn⟩ := mem_LN v hm
  simp only [Units.val_mk0] at hn
  have h1 : Irr v (((1 + 4 * ρ) * z - 1) / 4) := by
    refine h.perturb v ?_
    have : ((1 + 4 * ρ) * z - 1) / 4 - ρ = (1 + 4 * ρ) * (z - 1) / 4 := by ring
    rw [this, map_div₀, map_mul, hu, one_mul]
    exact (div_lt_one₀ (zero_lt_iff.2 (v_four_ne v))).2 hz
  obtain ⟨r, hr, h2⟩ := h1.aux2 v a
  have h3 : a ^ 2 - (1 + 4 * (((1 + 4 * ρ) * z - 1) / 4)) = θ * b ^ 2 := by
    linear_combination -hn
  rw [h3, map_mul, map_pow] at h2
  have hb : v b ≠ 0 := by
    intro hb
    rw [hb] at h2
    exact hr (by simpa using h2.symm)
  exact hθ (sq_cancel hb ⟨r, by rw [h2, sq]⟩)

private lemma nonnorm_unram (hs : Function.Surjective v) {θ y : K} (hy : v y = 1)
    (h1 : v (θ - y ^ 2) ≤ v 4) (h2 : ∀ x, v 4 ≤ v (θ - x ^ 2)) : ∃ α : Kˣ, α ∉ LN v θ := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have h4 := zero_lt_iff.2 (v_four_ne v)
  have hρ : v ((θ - y ^ 2) / (4 * y ^ 2)) ≤ 1 := by
    rw [map_div₀, map_mul, map_pow, hy, one_pow, mul_one]
    exact (div_le_one₀ h4).2 h1
  have hI : Irr v ((θ - y ^ 2) / (4 * y ^ 2)) := by
    refine ⟨hρ, fun X hX => le_antisymm ?_ ?_⟩
    · refine v.map_sub_le (v.map_add_le ?_ hX) hρ
      rw [map_pow]
      exact pow_le_one₀ zero_le hX
    · have h5 := h2 (y * (1 + 2 * X))
      have : θ - (y * (1 + 2 * X)) ^ 2
          = - (4 * (y ^ 2 * (X ^ 2 + X - (θ - y ^ 2) / (4 * y ^ 2)))) := by
        field_simp; ring
      rw [this, v.map_neg, map_mul, map_mul, map_pow, hy, one_pow, one_mul] at h5
      exact (le_mul_iff_one_le_right h4).1 h5
  obtain ⟨π, hπ⟩ := hs (WithZero.exp (-1))
  have hπ0 : π ≠ 0 := by rintro rfl; exact WithZero.exp_ne_zero (by rw [← hπ, map_zero])
  refine ⟨Units.mk0 _ hπ0, fun hm => ?_⟩
  obtain ⟨z, a, b, hz, hn⟩ := mem_LN v hm
  have h6 := hI.isSquare v a (y * b)
  have : a ^ 2 - (1 + 4 * ((θ - y ^ 2) / (4 * y ^ 2))) * (y * b) ^ 2 = π * z := by
    simp only [Units.val_mk0] at hn
    rw [hn]; field_simp; ring
  rw [this, map_mul, v_eq_one v (hz.trans_le (v_four v)), mul_one, hπ] at h6
  exact not_sq_exp h6

private lemma nonnorm_ram {ρ θ y : K} (h : Irr v ρ) (hθ : v θ = 1) (hy : v y = 1)
    (h1 : v 4 < v (θ - y ^ 2)) (h2 : ¬ IsSquare (v (θ - y ^ 2))) : ∃ α : Kˣ, α ∉ LN v θ := by
  have hu := h.unit v
  set Δ := 1 + 4 * ρ with hΔ
  obtain ⟨a, ha⟩ : ∃ a, a = Δ * y ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = θ - a := ⟨_, rfl⟩
  have hva : v a = 1 := by simp [ha, hu, hy]
  have hvb : v b = v (θ - y ^ 2) := by
    refine v_eq_of v (lt_of_le_of_lt ?_ h1)
    have : b - (θ - y ^ 2) = - (4 * (ρ * y ^ 2)) := by rw [hb, ha, hΔ]; ring
    rw [this, v.map_neg, map_mul, map_mul, map_pow, hy, one_pow, mul_one]
    exact mul_le_of_le_one_right' h.1
  rw [← hvb] at h1 h2
  have ha0 : a ≠ 0 := by rintro rfl; simp at hva
  have hb0 : b ≠ 0 := by rintro rfl; simp at h1
  refine ⟨Units.mk0 (-(a * b)) (by simp [ha0, hb0]), fun hm => ?_⟩
  obtain ⟨z, s, t, hz, hn⟩ := mem_LN v hm
  simp only [Units.val_mk0] at hn
  have key : ∀ ε : K, ε ^ 2 = 1 → v (s - ε * a) < v 2 := by
    intro ε hε
    by_contra hR
    push Not at hR
    have h6 := h.isSquare v (θ * t) (y * (s + ε * b))
    have h7 : (θ * t) ^ 2 - (1 + 4 * ρ) * (y * (s + ε * b)) ^ 2
        = b * ((s - ε * a) ^ 2 + θ * a * (z - 1)) := by
      have h8 : θ = a + b := by rw [hb]; ring
      rw [mul_pow y, ← mul_assoc, ← hΔ, ← ha]
      subst h8
      linear_combination (a + b) * hn - a * b * (a + b) * hε
    have h9 : v ((s - ε * a) ^ 2 + θ * a * (z - 1)) = v (s - ε * a) ^ 2 := by
      rw [← map_pow]
      refine v.map_add_eq_of_lt_left ?_
      rw [map_mul, map_mul, hθ, hva, one_mul, one_mul, map_pow]
      refine hz.trans_le ?_
      rw [v_four_eq]
      gcongr
    rw [h7, map_mul, h9] at h6
    exact h2 (sq_cancel ((zero_lt_iff.2 (v_two_ne v)).trans_le hR).ne' h6)
  have := v.map_sub_lt (key (-1) (by ring)) (key 1 (by ring))
  have h10 : s - -1 * a - (s - 1 * a) = 2 * a := by ring
  rw [h10, map_mul, hva, mul_one] at this
  exact lt_irrefl _ this

private lemma nonnorm_unit (hs : Function.Surjective v) {ρ : K} (h : Irr v ρ)
    (hp : v 2 < 1 → ∀ ε : K, v ε ≤ 1 → ∃ η, v (ε - η ^ 2) < 1) {θ : Kˣ} (hθ : v θ = 1)
    (hQ : θ ∉ Qv v) : ∃ α : Kˣ, α ∉ LN v θ := by
  have hl : ∀ x : K, v 4 ≤ v (θ - x ^ 2) := fun x => not_lt.1 fun hx => hQ (mem_Qv_of v hθ hx)
  have hl0 : ∀ x : K, v (θ - x ^ 2) ≠ 0 := fun x =>
    ((zero_lt_iff.2 (v_four_ne v)).trans_le (hl x)).ne'
  obtain ⟨_, ⟨y, rfl⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun m => ∃ y : K, WithZero.log (v (θ - y ^ 2)) = m)
    ⟨WithZero.log (v 4), by
      rintro _ ⟨y, rfl⟩
      exact (WithZero.log_le_log (v_four_ne v) (hl0 y)).2 (hl y)⟩ ⟨_, 0, rfl⟩
  have hm : ∀ x : K, v (θ - y ^ 2) ≤ v (θ - x ^ 2) := fun x =>
    (WithZero.log_le_log (hl0 y) (hl0 x)).1 (hmin _ ⟨x, rfl⟩)
  have hβ : v (θ - y ^ 2) ≤ 1 := by simpa [hθ] using hm 0
  have sq1 : ∀ x : K, v (x ^ 2) ≤ 1 → v x ≤ 1 := fun x hx => by
    rwa [map_pow, pow_le_one_iff_of_nonneg zero_le two_ne_zero] at hx
  have hy1 : v y ≤ 1 := by
    refine sq1 y ?_
    have := v.map_sub_le hθ.le hβ
    simpa using this
  have hy2 : v (θ - y ^ 2) < 1 → v y = 1 := fun h' => by
    have : v (y ^ 2) = v θ := v_eq_of v (by rwa [v.map_sub_swap, hθ])
    rwa [hθ, map_pow, pow_eq_one_iff_of_nonneg zero_le two_ne_zero] at this
  rcases (v_two v).eq_or_lt with h2 | h2
  · refine nonnorm_unram v hs (y := 1) (by simp) ?_ hl
    rw [v_four_eq, h2, one_pow]
    exact v.map_sub_le hθ.le (by simp)
  have h4 : v (4 : K) < 1 := by
    rw [v_four_eq]; exact pow_lt_one₀ zero_le h2 two_ne_zero
  rcases (hl y).eq_or_lt with h5 | h5
  · exact nonnorm_unram v hs (hy2 (h5 ▸ h4)) h5.ge hl
  have hns : ¬ IsSquare (v (θ - y ^ 2)) := by
    rintro ⟨r, hr⟩
    obtain ⟨c, rfl⟩ := hs r
    rw [← sq] at hr
    have hc : v c ≠ 0 := fun h0 => hl0 y (by simp [hr, h0])
    have hc0 : c ≠ 0 := by simpa using hc
    have hcp := zero_lt_iff.2 hc
    have hε : v ((θ - y ^ 2) / c ^ 2) = 1 := by
      rw [map_div₀, hr, map_pow, div_self (pow_ne_zero _ hc)]
    obtain ⟨η, hη⟩ := hp h2 _ hε.le
    have hη1 : v η ≤ 1 := by
      refine sq1 η ?_
      have := v.map_sub_le hε.le hη.le
      simpa using this
    have h6 : v 2 < v c := by
      rw [hr, v_four_eq] at h5
      exact lt_of_pow_lt_pow_left₀ 2 zero_le h5
    refine absurd (hm (y + c * η)) (not_le.2 ?_)
    have : θ - (y + c * η) ^ 2 = c ^ 2 * ((θ - y ^ 2) / c ^ 2 - η ^ 2) - c * (2 * (y * η)) := by
      field_simp; ring
    rw [this, hr]
    refine v.map_sub_lt ?_ ?_
    · rw [map_mul, map_pow]
      exact mul_lt_of_lt_one_right (pow_pos hcp 2) hη
    · rw [map_mul, sq]
      refine mul_lt_mul_of_pos_left (lt_of_le_of_lt ?_ h6) hcp
      rw [map_mul, map_mul]
      exact mul_le_of_le_one_right' (mul_le_one' hy1 hη1)
  refine nonnorm_ram v h hθ (hy2 (hβ.lt_of_ne fun h1 => hns ?_)) h5 hns
  rw [h1]
  exact IsSquare.one

private lemma nonnorm (hs : Function.Surjective v) {ρ : K} (h : Irr v ρ)
    (hp : v 2 < 1 → ∀ ε : K, v ε ≤ 1 → ∃ η, v (ε - η ^ 2) < 1) {θ : Kˣ}
    (hQ : θ ∉ Qv v) : ∃ α : Kˣ, α ∉ LN v θ := by
  by_cases hsq : IsSquare (v θ)
  · obtain ⟨r, hr⟩ := hsq
    obtain ⟨c, rfl⟩ := hs r
    have hc0 : c ≠ 0 := by rintro rfl; simp at hr
    have hc : v c ≠ 0 := by simpa using hc0
    obtain ⟨α, hα⟩ := nonnorm_unit v hs h hp (θ := θ / Units.mk0 c hc0 ^ 2)
      (by simp [hr, sq, hc]) (fun h' => hQ (by simpa using mul_mem h' (sq_mem_Qv v (Units.mk0 c hc0))))
    refine ⟨α, fun h' => hα ((sup_le_sup_right (?_ : Nm (θ : K) ≤ Nm _) (near4 v) :) h')⟩
    rintro x ⟨a, b, hx⟩
    refine ⟨a, b * c, ?_⟩
    rw [hx]; simp; field_simp
  · exact nonnorm_odd v h hsq

end loc

section nf
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private lemma val_alg (a : 𝓞 K) : v.valuation K (algebraMap _ K a) = v.intValuation a :=
  v.valuation_of_algebraMap a

private lemma val_le_one (a : 𝓞 K) : v.valuation K (algebraMap _ K a) ≤ 1 :=
  v.valuation_le_one a

private lemma val_le_iff (a : 𝓞 K) (n : ℕ) :
    v.valuation K (algebraMap _ K a) ≤ WithZero.exp (-(n : ℤ)) ↔ a ∈ v.asIdeal ^ n := by
  rw [val_alg, v.intValuation_le_pow_iff_mem]

private lemma val_lt_one_iff (a : 𝓞 K) :
    v.valuation K (algebraMap _ K a) < 1 ↔ a ∈ v.asIdeal := v.valuation_lt_one_iff_mem a

private lemma approx {x : K} (hx : v.valuation K x ≤ 1) {γ : ℤᵐ⁰} (h : γ ≠ 0) :
    ∃ a : 𝓞 K, v.valuation K (x - algebraMap _ K a) < γ := by
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hx (Units.mk0 γ h)
  exact ⟨a, by rwa [Valuation.map_sub_swap]⟩

private lemma fin_quot (n : ℕ) : Finite (𝓞 K ⧸ v.asIdeal ^ n) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n v.ne_bot)

private lemma exists_irr : ∃ ρ, Irr (v.valuation K) ρ := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have := v.isPrime
  have hns : ¬ Function.Surjective (fun x : 𝓞 K ⧸ v.asIdeal => x ^ 2 + x) := by
    rw [← Finite.injective_iff_surjective]
    intro h
    have := @h 0 (-1) (by simp)
    simp at this
  obtain ⟨r, hr⟩ := not_forall.1 hns
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨algebraMap _ K ρ, val_le_one v ρ, fun X hX => ?_⟩
  obtain ⟨a, ha⟩ := approx v hX one_ne_zero
  have h1 : v.valuation K (algebraMap _ K (a ^ 2 + a - ρ)) = 1 := by
    rw [v.valuation_eq_one_iff_notMem]
    intro h
    exact hr ⟨Ideal.Quotient.mk _ a, by simpa using Ideal.Quotient.eq.2 h⟩
  rw [← h1]
  refine v_eq_of _ ?_
  rw [h1]
  have : X ^ 2 + X - algebraMap _ K ρ - algebraMap _ K (a ^ 2 + a - ρ)
      = (X - algebraMap _ K a) * (X + algebraMap _ K a + 1) := by
    simp only [map_sub, map_add, map_pow]; ring
  rw [this, map_mul]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) ha
  exact Valuation.map_add_le _ (Valuation.map_add_le _ hX (val_le_one v a)) (by simp)

private lemma perfect (h2 : v.valuation K 2 < 1) (ε : K) (hε : v.valuation K ε ≤ 1) :
    ∃ η, v.valuation K (ε - η ^ 2) < 1 := by
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have := v.isPrime
  have h0 : (2 : 𝓞 K ⧸ v.asIdeal) = 0 := by
    have : (2 : 𝓞 K) ∈ v.asIdeal := (val_lt_one_iff v 2).1 (by rwa [map_ofNat])
    have := Ideal.Quotient.eq_zero_iff_mem.2 this
    rwa [map_ofNat] at this
  have hs : Function.Surjective (fun x : 𝓞 K ⧸ v.asIdeal => x ^ 2) := by
    rw [← Finite.injective_iff_surjective]
    intro x y h
    have h : x ^ 2 = y ^ 2 := h
    have : (x - y) ^ 2 = 0 := by linear_combination h + (y ^ 2 - x * y) * h0
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  obtain ⟨a, ha⟩ := approx v hε one_ne_zero
  obtain ⟨r, hr⟩ := hs (Ideal.Quotient.mk _ a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨algebraMap _ K b, ?_⟩
  have h1 : a - b ^ 2 ∈ v.asIdeal := Ideal.Quotient.eq.1 (by rw [← hr]; simp)
  have := Valuation.map_add_lt _ ha ((val_lt_one_iff v _).2 h1)
  convert this using 2
  simp

private lemma nonnorm' {θ : Kˣ} (hQ : θ ∉ Qv (v.valuation K)) :
    ∃ α : Kˣ, α ∉ LN (v.valuation K) θ := by
  obtain ⟨ρ, h⟩ := exists_irr v
  exact nonnorm _ (v.valuation_surjective K) h (perfect v) hQ

private noncomputable def ev : ℕ := (- WithZero.log (v.valuation K 2)).toNat

private lemma v_two_eq : v.valuation K 2 = WithZero.exp (-(ev v : ℤ)) := by
  have h0 := v_two_ne (v.valuation K)
  have : WithZero.log (v.valuation K 2) ≤ 0 :=
    (WithZero.log_le_iff_le_exp h0).2 (by simpa using v_two (v.valuation K))
  rw [ev, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]

private def Wv : Subgroup Kˣ where
  carrier := {x | v.valuation K x = 1}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simp_all
  inv_mem' := by intro a ha; simp_all

private lemma mem_Wv {x : Kˣ} : x ∈ Wv v ↔ v.valuation K x = 1 := Iff.rfl

private lemma mem_near_four_of_close {x y : Kˣ} (hx : v.valuation K x = 1)
    (h : v.valuation K (y - x) < v.valuation K 4) : x⁻¹ * y ∈ near4 (v.valuation K) := by
  rw [mem_near4]
  have : ((x⁻¹ * y : Kˣ) : K) - 1 = (y - x) / x := by push_cast; field_simp
  rwa [this, map_div₀, hx, div_one]

private lemma relIndex_Qv : (Qv (v.valuation K)).relIndex (Wv v) ≠ 0 ∧
    (Qv (v.valuation K)).relIndex (Wv v) ≤ 2 * Ideal.absNorm (v.asIdeal ^ ev v) := by
  have h40 := v_four_ne (v.valuation K)
  have h20 := v_two_ne (v.valuation K)
  have h2p := zero_lt_iff.2 h20
  set N := (near4 (v.valuation K)).subgroupOf (Wv v) with hN
  have hfin : N.index ≠ 0 := by
    obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt h40
    have := fin_quot v k
    refine (relIndex_le_card' (α := 𝓞 K ⧸ v.asIdeal ^ k) _ (Wv v)
      (fun x q => ∃ a, Ideal.Quotient.mk _ a = q ∧
        v.valuation K (x - algebraMap _ K a) < v.valuation K 4) ?_ ?_).1
    · intro x hx
      obtain ⟨a, ha⟩ := approx v (le_of_eq hx) h40
      exact ⟨_, a, rfl, ha⟩
    · rintro x hx y - _ ⟨a, rfl, ha⟩ ⟨b, hab, hb⟩
      refine mem_near_four_of_close v hx ?_
      have h1 := ((val_le_iff v _ k).2 (Ideal.Quotient.eq.1 hab)).trans_lt hk
      have := Valuation.map_sub_lt _ (Valuation.map_add_lt _ hb h1) ha
      convert this using 2
      simp
  have h1 := index_sup_range N (powMonoidHom 2) hfin (fun x hx => pow_mem hx 2)
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : v.valuation K π ≠ 0 := by rw [hπ]; exact WithZero.exp_ne_zero
  have hπ1 : v.valuation K π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0' : π ≠ 0 := by simpa using hπ0
  have := fin_quot v (ev v)
  have h2 := relIndex_le_card' (α := ℤˣ × (𝓞 K ⧸ v.asIdeal ^ ev v)) N (N.comap (powMonoidHom 2))
    (fun x q => ∃ a, Ideal.Quotient.mk _ a = q.2 ∧
        v.valuation K (((q.1 : ℤ) : K) * ((x : Kˣ) : K) - 1 - 2 * π * algebraMap _ K a)
          < v.valuation K 4) ?_ ?_
  · rw [← h1, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int] at h2
    have hle : N ⊔ (powMonoidHom 2).range ≤ (Qv (v.valuation K)).subgroupOf (Wv v) := by
      refine sup_le (Subgroup.subgroupOf_mono _ le_sup_left) ?_
      rintro _ ⟨y, rfl⟩
      exact sq_mem_Qv _ _
    have h3 := Subgroup.index_dvd_of_le hle
    exact ⟨ne_zero_of_dvd_ne_zero h2.1 h3, (Nat.le_of_dvd (Nat.pos_of_ne_zero h2.1) h3).trans h2.2⟩
  · rintro ⟨x, hx1⟩ hx
    have hx : v.valuation K ((x : K) ^ 2 - 1) < v.valuation K 4 := hx
    have : ∃ s : ℤˣ, v.valuation K (((s : ℤ) : K) * x - 1) < v.valuation K 2 := by
      by_contra hc
      push Not at hc
      have h3 := mul_le_mul' (hc 1) (hc (-1))
      rw [← sq, ← v_four_eq, ← map_mul, ← Valuation.map_neg _ (_ * _)] at h3
      refine absurd hx (not_lt.2 ?_)
      convert h3 using 2
      simp; ring
    obtain ⟨s, hs⟩ := this
    have h3 : v.valuation K ((((s : ℤ) : K) * x - 1) / (2 * π)) ≤ 1 := by
      rw [map_div₀, map_mul, div_le_one₀ (zero_lt_iff.2 (mul_ne_zero h20 hπ0)),
        ← WithZero.lt_mul_exp_iff_le (mul_ne_zero h20 hπ0), hπ, mul_assoc, ← WithZero.exp_add]
      simpa using hs
    obtain ⟨a, ha⟩ := approx v h3 h20
    refine ⟨(s, _), a, rfl, ?_⟩
    have : ((s : ℤ) : K) * x - 1 - 2 * π * algebraMap _ K a
      = 2 * (π * ((((s : ℤ) : K) * x - 1) / (2 * π) - algebraMap _ K a)) := by field_simp
    simp only
    rw [this, map_mul, map_mul, v_four_eq, sq]
    exact mul_lt_mul_of_pos_left (lt_of_le_of_lt (mul_le_of_le_one_left' hπ1.le) ha) h2p
  · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - ⟨s, _⟩ ⟨a, rfl, ha⟩ ⟨b, hab, hb⟩
    refine mem_near_four_of_close v hx ?_
    have h1 := (val_le_iff v _ _).2 (Ideal.Quotient.eq.1 hab)
    rw [← v_two_eq] at h1
    have h3 : v.valuation K (2 * (π * algebraMap _ K (b - a))) < v.valuation K 4 := by
      rw [map_mul, map_mul, v_four_eq, sq]
      refine mul_lt_mul_of_pos_left (lt_of_le_of_lt (mul_le_mul_right h1 _) ?_) h2p
      exact mul_lt_of_lt_one_left h2p hπ1
    have h4 := Valuation.map_sub_lt _ (Valuation.map_add_lt _ hb h3) ha
    have h5 : v.valuation K ((y : K) - x) = v.valuation K (((s : ℤ) : K) * (y - x)) := by
      rcases Int.units_eq_one_or s with rfl | rfl <;> simp [Valuation.map_sub_swap]
    rw [h5]
    convert h4 using 2
    simp only [map_sub]; ring

private lemma index_Qv : (Qv (v.valuation K)).index ≠ 0 ∧
    (Qv (v.valuation K)).index ≤ 4 * Ideal.absNorm (v.asIdeal ^ ev v) := by
  have h1 := relIndex_Qv v
  have h2 := relIndex_le_card (Qv (v.valuation K) ⊔ Wv v) ⊤
    (fun x => ((WithZero.log (v.valuation K ((x : Kˣ) : K)) : ℤ) : ZMod 2)) ?_
  · rw [Subgroup.relIndex_top_right, Nat.card_zmod] at h2
    rw [← Subgroup.relIndex_mul_index (le_sup_left : _ ≤ Qv (v.valuation K) ⊔ Wv v),
      Subgroup.relIndex_sup_left]
    refine ⟨mul_ne_zero h1.1 h2.1, (Nat.mul_le_mul h1.2 h2.2).trans (le_of_eq (by ring))⟩
  · rintro ⟨x, hx'⟩ ⟨y, hy'⟩ h
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).1 h
    obtain ⟨c, hc⟩ := v.valuation_surjective K (WithZero.exp k)
    have hc0 : c ≠ 0 := by rintro rfl; exact WithZero.exp_ne_zero (by rw [← hc, map_zero])
    refine Subgroup.mem_sup.2 ⟨_, sq_mem_Qv _ (Units.mk0 c hc0), x⁻¹ * y / Units.mk0 c hc0 ^ 2, ?_,
      by simp⟩
    have hx : v.valuation K x ≠ 0 := by simp
    have hy : v.valuation K y ≠ 0 := by simp
    rw [mem_Wv]
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.val_mk0, map_div₀, map_mul, map_inv₀, map_pow, hc] at hk ⊢
    rw [← WithZero.exp_log hx, ← WithZero.exp_log hy, ← WithZero.exp_neg, ← WithZero.exp_add,
      ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_eq_one]
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at hk ⊢
    omega

private lemma mul_mem_Qv (h2 : v.valuation K 2 = 1) {x y : Kˣ} (hx : v.valuation K x = 1)
    (hy : v.valuation K y = 1) (hx' : x ∉ Qv (v.valuation K)) (hy' : y ∉ Qv (v.valuation K)) :
    x * y ∈ Qv (v.valuation K) := by
  have h := relIndex_Qv v
  have he : ev v = 0 := by
    have := v_two_eq v
    rw [h2, eq_comm, WithZero.exp_eq_one] at this
    omega
  rw [he] at h
  simp only [pow_zero, map_one, mul_one] at h
  have h1 : (Qv (v.valuation K)).relIndex (Wv v) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hx' (h hx)
  have h3 : ((Qv (v.valuation K)).subgroupOf (Wv v)).index = 2 := by
    rw [← Subgroup.relIndex]; omega
  exact (Subgroup.mul_mem_iff_of_index_two h3 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).2
    (iff_of_false hx' hy')

private lemma index_QS (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (⨅ v ∈ S, Qv (v.valuation K)).index ≠ 0 ∧
    (⨅ v ∈ S, Qv (v.valuation K)).index ≤ 4 ^ S.card * 2 ^ finrank ℚ K := by
  rw [iInf_subtype']
  refine ⟨Subgroup.index_iInf_ne_zero fun i => (index_Qv _).1,
    (Subgroup.index_iInf_le _).trans ?_⟩
  refine (Finset.prod_le_prod' (fun i _ => (index_Qv i.1).2)).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← map_prod]
  refine Nat.mul_le_mul_left _ (Nat.le_of_dvd (by positivity) ?_)
  rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
  refine map_dvd _ (Finset.prod_dvd_of_coprime ?_ ?_)
  · intro i _ j _ hij
    exact HeightOneSpectrum.isCoprime_pow_of_ne _ _ (fun h => hij (Subtype.ext h)) _ _
  · intro i _
    rw [Ideal.dvd_span_singleton, ← val_le_iff, ← v_two_eq]
    simp [map_ofNat]

private lemma exists_den (x : K) :
    ∃ a d : 𝓞 K, d ≠ 0 ∧ x * algebraMap _ K d = algebraMap _ K a := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h0 := nonZeroDivisors.ne_zero hd
  exact ⟨a, d, h0, div_mul_cancel₀ _ (by simpa using h0)⟩

private lemma weak_approx (S : Finset (HeightOneSpectrum (𝓞 K))) (α : Kˣ) :
    ∃ x : Kˣ, α⁻¹ * x ∈ Qv (v.valuation K) ∧ ∀ w ∈ S, w ≠ v → x ∈ Qv (w.valuation K) := by
  classical
  obtain ⟨a, d, hd, h⟩ := exists_den (α : K)
  have hd' : algebraMap _ K d ≠ 0 := by simpa using hd
  set D := Units.mk0 _ hd' with hD
  have hA : algebraMap _ K (a * d) = ((α * D ^ 2 : Kˣ) : K) := by
    rw [map_mul, ← h, hD]; simp [sq, mul_assoc]
  have h0 : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K 4 * w.valuation K (α * D ^ 2 : Kˣ) ≠ 0 :=
    fun w => mul_ne_zero (v_four_ne _) (by simp)
  choose k hk using fun w => WithZero.exists_exp_neg_natCast_lt (h0 w)
  obtain ⟨y, hy⟩ := exists_forall_sub_mem_ideal (s := insert v S) (fun w => w.asIdeal) k
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if w.1 = v then a * d else 1)
  have h1 := ((val_le_iff _ _ _).2 (hy v (Finset.mem_insert_self _ _))).trans_lt (hk v)
  simp only [if_true, map_sub, hA] at h1
  have hy0 : algebraMap _ K y ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg] at h1
    exact absurd h1 (not_lt.2 (mul_le_of_le_one_left' (v_four _)))
  refine ⟨Units.mk0 _ hy0, (mem_Qv _).2 ⟨(α * D ^ 2)⁻¹ * Units.mk0 _ hy0, ?_, D, ?_⟩, ?_⟩
  · rw [mem_near4]
    have : (((α * D ^ 2)⁻¹ * Units.mk0 _ hy0 : Kˣ) : K) - 1
        = (algebraMap _ K y - (α * D ^ 2 : Kˣ)) / (α * D ^ 2 : Kˣ) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]; field_simp
    rwa [this, map_div₀, div_lt_iff₀ (zero_lt_iff.2 (by simp))]
  · rw [mul_inv, mul_right_comm _ _ (D ^ 2), inv_mul_cancel_right]
  · intro w hw hwv
    have h2 := ((val_le_iff _ _ _).2 (hy w (Finset.mem_insert_of_mem hw))).trans_lt (hk w)
    simp only [if_neg hwv, map_sub, map_one] at h2
    refine Subgroup.mem_sup_left ((mem_near4 _).2 (h2.trans_le (mul_le_of_le_one_right' ?_)))
    rw [← hA]
    exact val_le_one _ _

end nf

section su
variable {K : Type*} [Field K] [NumberField K]

private def US (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ where
  carrier := {x | ∀ v ∉ S, v.valuation K x = 1}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb v hv; simp [ha v hv, hb v hv]
  inv_mem' := by intro a ha v hv; simp [ha v hv]

private lemma US_mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) : US S ≤ US T :=
  fun _ hx v hv => hx v fun h' => hv (h h')

private lemma neg_one_mem_US (S : Finset (HeightOneSpectrum (𝓞 K))) : -1 ∈ US S := by
  intro v _; simp

private lemma exists_US (x : Kˣ) : ∃ S, x ∈ US S := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) (x : K)
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) (x : K)⁻¹
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, HeightOneSpectrum.Support, Set.mem_setOf_eq,
    not_or, not_lt, map_inv₀] at hv
  exact le_antisymm hv.1 ((inv_le_one₀ (zero_lt_iff.2 (by simp))).1 hv.2)

private lemma root_mem_US {S : Finset (HeightOneSpectrum (𝓞 K))} {x : Kˣ} (h : x ^ 2 ∈ US S) :
    x ∈ US S := by
  intro v hv
  have := h v hv
  rwa [Units.val_pow_eq_pow_val, map_pow, pow_eq_one_iff_of_nonneg zero_le two_ne_zero] at this

private lemma not_mem_of_pow {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (n : ℕ) :
    ∃ a ∈ v.asIdeal ^ n, w.valuation K (algebraMap _ K a) = 1 := by
  by_contra hc
  push Not at hc
  have h1 : v.asIdeal ^ n ≤ w.asIdeal := fun a ha => by
    by_contra h'
    exact hc a ha (w.valuation_eq_one_iff_notMem.2 h')
  have h2 := (HeightOneSpectrum.isCoprime_pow_of_ne v w h.symm n 1)
  rw [Ideal.isCoprime_iff_sup_eq, pow_one, sup_eq_right.2 h1] at h2
  exact w.isPrime.ne_top h2

private lemma exists_gen (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : Kˣ, v.valuation K c = WithZero.exp (-(Nat.card (ClassGroup (𝓞 K)) : ℤ)) ∧
      ∀ w, w ≠ v → w.valuation K c = 1 := by
  set h := Nat.card (ClassGroup (𝓞 K))
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1 := by
    have : (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨_, hv⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one']
  obtain ⟨c, hc⟩ := (ClassGroup.mk0_eq_one_iff _).1 h1
  have hc : v.asIdeal ^ h = Ideal.span {c} := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero h v.ne_bot (by simpa using hc)
  refine ⟨Units.mk0 (algebraMap _ K c) (by simpa using hc0), ?_, fun w hw => ?_⟩
  · rw [Units.val_mk0, val_alg, v.intValuation_eq_exp_neg_multiplicity hc0, ← hc,
      multiplicity_pow_self_of_prime v.prime]
  · obtain ⟨a, ha, h2⟩ := not_mem_of_pow hw h
    rw [hc, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_mul] at h2
    refine le_antisymm (val_le_one _ _) ?_
    rw [← h2]
    exact mul_le_of_le_one_left' (val_le_one _ _)

private lemma US_rank (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.Finite ℤ (Additive (US S)) ∧ finrank ℤ (Additive (US S)) = Units.rank K + S.card := by
  classical
  let φ : Additive (US S) →ₗ[ℤ] (S → ℤ) := AddMonoidHom.toIntLinearMap
    { toFun := fun x v => WithZero.log (v.1.valuation K ((x.toMul : Kˣ) : K))
      map_zero' := by ext; simp
      map_add' := by
        intro x y; ext v
        simp [WithZero.log_mul] }
  have hφ : ∀ x v, φ x v = WithZero.log (v.1.valuation K ((x.toMul : Kˣ) : K)) := fun _ _ => rfl
  have hu : ∀ (u : (𝓞 K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      v.valuation K (algebraMap _ K (u : 𝓞 K)) = 1 := fun u v =>
    v.valuation_eq_one_iff_notMem.2 fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  let ψ : Additive (𝓞 K)ˣ →ₗ[ℤ] Additive (US S) := AddMonoidHom.toIntLinearMap
    (MonoidHom.toAdditive ((Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).codRestrict (US S)
      fun u v _ => hu u v))
  have hψ : ∀ u, (((ψ u).toMul : Kˣ) : K) = algebraMap _ K (u.toMul : 𝓞 K) := fun _ => rfl
  have hinj : Function.Injective ψ := fun x y h => by
    have := hψ x
    rw [h, hψ] at this
    exact Additive.toMul.injective (Units.ext (IsFractionRing.injective _ K this.symm))
  have hker : LinearMap.range ψ = LinearMap.ker φ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      ext v
      rw [hφ, hψ, hu]; simp
    · intro hx
      have h1 : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x.toMul : Kˣ) : K) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have := congrFun hx ⟨v, hv⟩
          rw [hφ] at this
          rw [← WithZero.exp_log (x := v.valuation K ((x.toMul : Kˣ) : K)) (by simp), this]
          simp
        · exact x.toMul.2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => (h1 v).le
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
        ((x.toMul : Kˣ) : K)⁻¹ fun v => by simp [h1 v]
      have hab : a * b = 1 := IsFractionRing.injective _ K (by rw [map_mul, ha, hb]; simp)
      exact ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩, Subtype.ext (Units.ext ha)⟩
  have hfin : Module.Finite ℤ (Additive (US S)) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, ← hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine ⟨hfin, ?_⟩
  have h1 := (LinearMap.ker φ).finrank_quotient_add_finrank
  rw [φ.quotKerEquivRange.finrank_eq, ← hker, LinearMap.finrank_range_of_inj hinj,
    Units.finrank_eq] at h1
  have h2 := (LinearMap.range φ).finrank_quotient_add_finrank
  have h3 : finrank ℤ ((S → ℤ) ⧸ LinearMap.range φ) = 0 := by
    rw [Module.finrank_eq_zero_iff_isTorsion]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨⟨-(Nat.card (ClassGroup (𝓞 K)) : ℤ), mem_nonZeroDivisors_of_ne_zero
      (by simpa using Nat.card_pos.ne')⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      pi_eq_sum_univ' x, Finset.smul_sum]
    refine Submodule.sum_mem _ fun v _ => ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc, hc'⟩ := exists_gen v.1
    refine ⟨Additive.ofMul ⟨c, fun w hw => hc' w fun h => hw (h ▸ v.2)⟩, ?_⟩
    ext w
    rw [hφ]
    by_cases hw : w = v
    · subst hw; simp [hc]
    · simp [hc' w fun h => hw (Subtype.ext h), hw]
  rw [h3] at h2
  simp only [finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  omega

private lemma index_sq_US [IsTotallyComplex K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powMonoidHom (α := US S) 2).range.index = 2 ^ (InfinitePlace.nrComplexPlaces K + S.card) := by
  obtain ⟨h1, h2⟩ := US_rank S
  rw [index_sq _ (neg_one_mem_US S), h2, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  have := IsTotallyComplex.finrank K
  have := finrank_pos (R := ℚ) (M := K)
  congr 1
  omega

private def Good (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  (∀ v ∉ S, v.valuation K 2 = 1) ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∃ c ∈ I, c ≠ 0 ∧
    ∀ v ∉ S, ∀ a ∈ I, v.valuation K (algebraMap _ K a) ≤ v.valuation K (algebraMap _ K c)

private lemma Good.mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (h : S ⊆ T) :
    Good T := by
  refine ⟨fun v hv => hS.1 v fun h' => hv (h h'), fun I hI => ?_⟩
  obtain ⟨c, hc, h0, h1⟩ := hS.2 I hI
  exact ⟨c, hc, h0, fun v hv => h1 v fun h' => hv (h h')⟩

private lemma exists_reps (R : Type*) [CommRing R] [IsDedekindDomain R] :
    ∃ j : ClassGroup R → R, (∀ C, j C ≠ 0) ∧ ∀ I : Ideal R, I ≠ ⊥ → ∃ C, ∃ c ∈ I, c ≠ 0 ∧
      ∀ a ∈ I, ∃ b, b * c = a * j C := by
  have h0 : ∀ C : ClassGroup R, ∃ j : R, j ≠ 0 ∧ ∀ I : nonZeroDivisors (Ideal R),
      C = (ClassGroup.mk0 I)⁻¹ → ∃ c ∈ I.1, c ≠ 0 ∧ ∀ a ∈ I.1, ∃ b, b * c = a * j := by
    intro C
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective C
    obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero J)
    refine ⟨j, hj0, fun I hI => ?_⟩
    obtain ⟨c, hc0, hc⟩ := ClassGroup.mk0_eq_mk0_inv_iff.1 hI
    obtain ⟨I, hI'⟩ := I
    obtain ⟨J, hJ'⟩ := J
    have hc : J * I = Ideal.span {c} := hc
    have hc1 : c ∈ J * I := by rw [hc]; exact Ideal.mem_span_singleton_self c
    refine ⟨c, Ideal.mul_le_right hc1, hc0, fun a ha => ?_⟩
    rw [← Ideal.mem_span_singleton', ← hc, mul_comm a]
    exact Ideal.mul_mem_mul hj ha
  choose j hj0 hj using h0
  exact ⟨j, hj0, fun I hI => ⟨_, hj _ ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ rfl⟩⟩

private lemma exists_good : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), Good S := by
  classical
  obtain ⟨j, hj0, hj⟩ := exists_reps (𝓞 K)
  have hj1 : ∀ C, algebraMap _ K (j C) ≠ 0 := fun C => by simpa using hj0 C
  choose T hT using fun C => exists_US (Units.mk0 _ (hj1 C))
  obtain ⟨T2, hT2⟩ := exists_US (Units.mk0 (2 : K) two_ne_zero)
  refine ⟨T2 ∪ Finset.univ.biUnion T, fun v hv => hT2 v fun h => hv (Finset.mem_union_left _ h),
    fun I hI => ?_⟩
  obtain ⟨C, c, hc, hc0, h⟩ := hj I hI
  refine ⟨c, hc, hc0, fun v hv a ha => ?_⟩
  obtain ⟨b, hb⟩ := h a ha
  have h3 : v.valuation K (algebraMap _ K (j C)) = 1 := hT C v fun h =>
    hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨C, Finset.mem_univ _, h⟩))
  have h4 : v.valuation K (algebraMap _ K (b * c)) = v.valuation K (algebraMap _ K (a * j C)) := by
    rw [hb]
  rw [map_mul, map_mul, map_mul, map_mul, h3, mul_one] at h4
  rw [← h4]
  exact mul_le_of_le_one_left' (val_le_one _ _)

private lemma Good.gen {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) {a b : K}
    (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ c : Kˣ, ∀ v ∉ S, v.valuation K c = max (v.valuation K a) (v.valuation K b) := by
  obtain ⟨a', d, hd, h1⟩ := exists_den a
  obtain ⟨b', e, he, h2⟩ := exists_den b
  have hd' : algebraMap _ K d ≠ 0 := by simpa using hd
  have he' : algebraMap _ K e ≠ 0 := by simpa using he
  have h3 : algebraMap _ K (a' * e) = a * algebraMap _ K (d * e) := by
    rw [map_mul, map_mul, ← h1, mul_assoc]
  have h4 : algebraMap _ K (b' * d) = b * algebraMap _ K (d * e) := by
    rw [map_mul, map_mul, ← h2]; ring
  have hde : algebraMap _ K (d * e) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hd' he'
  obtain ⟨c, hc, hc0, h5⟩ := hS.2 (Ideal.span {a' * e, b' * d}) (by
    rw [Ne, Ideal.span_eq_bot]
    intro h0
    rw [h0 (a' * e) (by simp), map_zero] at h3
    rw [h0 (b' * d) (by simp), map_zero] at h4
    rcases h with h | h
    · exact mul_ne_zero h hde h3.symm
    · exact mul_ne_zero h hde h4.symm)
  refine ⟨Units.mk0 (algebraMap _ K c / algebraMap _ K (d * e))
    (div_ne_zero (by simpa using hc0) hde), fun v hv => ?_⟩
  have hp : 0 < v.valuation K (algebraMap _ K (d * e)) := zero_lt_iff.2 (by simpa using hde)
  rw [Units.val_mk0, map_div₀, div_eq_iff hp.ne', max_mul, ← map_mul, ← map_mul,
    ← h3, ← h4]
  refine le_antisymm ?_ (max_le (h5 v hv _ (Ideal.subset_span (by simp)))
    (h5 v hv _ (Ideal.subset_span (by simp))))
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.1 hc
  rw [map_add, map_mul _ x, map_mul _ y]
  refine (Valuation.map_add _ _ _).trans (max_le_max ?_ ?_) <;>
  · rw [map_mul]
    exact mul_le_of_le_one_left' (val_le_one _ _)

private lemma Good.single {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (α : Kˣ) :
    ∃ c : Kˣ, v.valuation K c = v.valuation K α ∧ ∀ w ∉ S, w ≠ v → w.valuation K c = 1 := by
  have key : ∀ n : ℕ, ∃ c : Kˣ, v.valuation K c = WithZero.exp (-(n : ℤ)) ∧
      ∀ w ∉ S, w ≠ v → w.valuation K c = 1 := by
    intro n
    obtain ⟨c, hc, hc0, h1⟩ := hS.2 _ (pow_ne_zero n v.ne_bot)
    refine ⟨Units.mk0 (algebraMap _ K c) (by simpa using hc0), le_antisymm ((val_le_iff _ _ _).2 hc) ?_,
      fun w hw hwv => le_antisymm (val_le_one _ _) ?_⟩
    · obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
      have h2 : v.valuation K (algebraMap _ K (π ^ n)) = WithZero.exp (-(n : ℤ)) := by
        rw [val_alg, map_pow, hπ, ← WithZero.exp_nsmul]; simp
      rw [← h2]
      exact h1 v hv _ ((val_le_iff _ _ _).1 h2.le)
    · obtain ⟨a, ha, h2⟩ := not_mem_of_pow hwv n
      rw [← h2]
      exact h1 w hw a ha
  obtain ⟨c, hc, hc'⟩ := key 1
  refine ⟨c ^ (- WithZero.log (v.valuation K α)), ?_, fun w hw hwv => ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hc, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log]
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hc' w hw hwv, one_zpow]

end su

section ext
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private lemma val_under (w : HeightOneSpectrum (𝓞 L)) : ∃ e : ℕ, e ≠ 0 ∧ ∀ x : K,
    w.valuation L (algebraMap K L x) = (w.under (𝓞 K)).valuation K x ^ e := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  refine ⟨_, ?_, fun x => (HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w x).symm⟩
  intro h0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (w.under (𝓞 K)).ne_bot
  have h1 := HeightOneSpectrum.intValuation_liesOver (w.under (𝓞 K)) w a
  rw [h0, pow_zero, eq_comm, HeightOneSpectrum.intValuation_eq_one_iff] at h1
  exact h1 ha

private lemma val_lt (w : HeightOneSpectrum (𝓞 L)) {x y : K} :
    w.valuation L (algebraMap K L x) < w.valuation L (algebraMap K L y) ↔
    (w.under (𝓞 K)).valuation K x < (w.under (𝓞 K)).valuation K y := by
  obtain ⟨e, he, h⟩ := val_under (K := K) w
  rw [h, h, pow_lt_pow_iff_left₀ zero_le zero_le he]

private lemma val_eq_one (w : HeightOneSpectrum (𝓞 L)) {x : K} :
    w.valuation L (algebraMap K L x) = 1 ↔ (w.under (𝓞 K)).valuation K x = 1 := by
  obtain ⟨e, he, h⟩ := val_under (K := K) w
  rw [h, pow_eq_one_iff_of_nonneg zero_le he]

private lemma map_mem_Qv (w : HeightOneSpectrum (𝓞 L)) {x : Kˣ}
    (h : x ∈ Qv ((w.under (𝓞 K)).valuation K)) :
    Units.map (algebraMap K L : K →* L) x ∈ Qv (w.valuation L) := by
  obtain ⟨z, hz, y, rfl⟩ := (mem_Qv _).1 h
  refine (mem_Qv _).2 ⟨Units.map (algebraMap K L : K →* L) z, ?_,
    Units.map (algebraMap K L : K →* L) y, by simp⟩
  have := (val_lt w).2 ((mem_near4 _).1 hz)
  rw [map_sub, map_one, map_ofNat] at this
  exact this

private lemma eq_of_le_exp {x y : ℤᵐ⁰} (hx : x ≤ 1) (hy : y ≤ 1)
    (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ)) ↔ y ≤ WithZero.exp (-(n : ℤ))) : x = y := by
  have key : ∀ x y : ℤᵐ⁰, y ≤ 1 →
      (∀ n : ℕ, y ≤ WithZero.exp (-(n : ℤ)) → x ≤ WithZero.exp (-(n : ℤ))) → x ≤ y := by
    intro x y hy h
    by_cases hy0 : y = 0
    · by_contra hc
      obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt (x := x) (by rintro rfl; simp at hc)
      exact absurd (h k (by simp [hy0])) (not_le.2 hk)
    · have h1 : WithZero.log y ≤ 0 := (WithZero.log_le_iff_le_exp hy0).2 (by simpa using hy)
      have h2 : y = WithZero.exp (-((- WithZero.log y).toNat : ℤ)) := by
        rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hy0]
      exact (h _ h2.le).trans h2.ge
  exact le_antisymm (key _ _ hy fun n => (h n).2) (key _ _ hx fun n => (h n).1)

private lemma exists_conj (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 K) = w.under (𝓞 K) ∧
      ∀ x, w'.valuation L x = w.valuation L (σ x) := by
  let e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  have he : ∀ a, algebraMap _ L (e a) = σ (algebraMap _ L a) := fun _ => rfl
  let w' := HeightOneSpectrum.comap (e : 𝓞 L →+* 𝓞 L) e.surjective w
  have h1 : ∀ a : 𝓞 L, w'.valuation L (algebraMap _ L a) = w.valuation L (σ (algebraMap _ L a)) := by
    intro a
    rw [← he]
    refine eq_of_le_exp (val_le_one _ _) (val_le_one _ _) fun n => ?_
    rw [val_le_iff, val_le_iff]
    show a ∈ (w.asIdeal.comap (e : 𝓞 L →+* 𝓞 L)) ^ n ↔ _
    rw [Ideal.comap_coe, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  refine ⟨w', ?_, fun x => ?_⟩
  · ext a
    show e (algebraMap _ _ a) ∈ w.asIdeal ↔ algebraMap _ _ a ∈ w.asIdeal
    have : e (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap _ _ a :=
      Subtype.ext (σ.commutes (algebraMap _ K a))
    rw [this]
  · obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    rw [map_div₀, map_div₀, map_div₀, h1, h1]

variable (L) in
private lemma exists_over (v : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := by
  have := v.isMaximal
  obtain ⟨P, hP, h⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  exact ⟨⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
    HeightOneSpectrum.ext h.over.symm⟩

variable (L) in
private lemma exists_SL (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S := by
  have : ((fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) ⁻¹' S).Finite := by
    refine S.finite_toSet.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage (f := HeightOneSpectrum.asIdeal)
      (fun _ _ _ _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  exact ⟨this.toFinset, fun w => by simp⟩

private lemma split {θ : Kˣ} {r : L} (hr : r ^ 2 = algebraMap K L θ) (σ : L ≃ₐ[K] L)
    (hσ : σ r = -r) {v : HeightOneSpectrum (𝓞 K)} (h : θ ∈ Qv (v.valuation K)) :
    ∃ w w' : HeightOneSpectrum (𝓞 L), w ≠ w' ∧ w.under (𝓞 K) = v ∧ w'.under (𝓞 K) = v := by
  obtain ⟨w, rfl⟩ := exists_over L v
  obtain ⟨w', h1, h2⟩ := exists_conj σ w
  refine ⟨w, w', ?_, rfl, h1⟩
  rintro rfl
  obtain ⟨z, hz, y, rfl⟩ := (mem_Qv _).1 h
  have hy : algebraMap K L y ≠ 0 := by simp
  have h3 := (val_lt w).2 ((mem_near4 _).1 hz)
  rw [map_ofNat] at h3
  set s := r / algebraMap K L y with hs
  have h4 : w.valuation L (1 + s) = w.valuation L (1 - s) := by
    rw [h2, hs, map_add, map_one, map_div₀, hσ, σ.commutes, neg_div, sub_eq_add_neg]
  have h5 : algebraMap K L (z - 1) = - ((1 + s) * (1 - s)) := by
    have : s ^ 2 = algebraMap K L z := by
      rw [hs, div_pow, hr]; simp
    rw [map_sub, map_one, ← this]; ring
  rw [h5, Valuation.map_neg, map_mul, ← h4, v_four_eq, ← sq] at h3
  have h6 := lt_of_pow_lt_pow_left₀ 2 zero_le h3
  have h7 := Valuation.map_add_lt _ h6 (h4 ▸ h6)
  have : 1 + s + (1 - s) = 2 := by ring
  rw [this] at h7
  exact lt_irrefl _ h7

private lemma card_SL {θ : Kˣ} {r : L} (hr : r ^ 2 = algebraMap K L θ) (σ : L ≃ₐ[K] L)
    (hσ : σ r = -r) {S P : Finset (HeightOneSpectrum (𝓞 K))} (hP : P ⊆ S)
    (h : ∀ v ∈ P, θ ∈ Qv (v.valuation K)) {T : Finset (HeightOneSpectrum (𝓞 L))}
    (hT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S) : S.card + P.card ≤ T.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => w.under (𝓞 K)) (s := T) (t := S)
    (fun w hw => (hT w).1 hw)]
  have : S.card + P.card = ∑ v ∈ S, (1 + if v ∈ P then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hP]; simp
  rw [this]
  refine Finset.sum_le_sum fun v hv => ?_
  split_ifs with hvP
  · obtain ⟨w, w', h1, rfl, h3⟩ := split hr σ hσ (h v hvP)
    exact Finset.one_lt_card.2 ⟨w, by simp [hT, hv], w', by simp [hT, hv, h3], h1⟩
  · obtain ⟨w, rfl⟩ := exists_over L v
    exact Finset.card_pos.2 ⟨w, by simp [hT, hv]⟩

end ext

private lemma finrank_le_add {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module.Finite ℤ A] [Module.Finite ℤ B] [Module.Finite ℤ C] (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (h : LinearMap.ker g ≤ LinearMap.range f) : finrank ℤ B ≤ finrank ℤ A + finrank ℤ C := by
  have h1 := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [g.quotKerEquivRange.finrank_eq] at h1
  have h2 := Submodule.finrank_mono h
  have h3 := LinearMap.finrank_range_le f
  have h4 := Submodule.finrank_le (LinearMap.range g)
  omega

section ct
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private lemma exists_unit {θ : Kˣ} {r : L} (hr : r ^ 2 = algebraMap K L θ) (σ : L ≃ₐ[K] L)
    (hσ : σ r = -r) (hb : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r)
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (hθ : θ ∈ US S)
    {T : Finset (HeightOneSpectrum (𝓞 L))} (hT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S)
    {u : Lˣ} (hu : u ∈ US T) (hu1 : (u : L) * σ u = 1) : ∃ y ∈ US T, (u : L) * σ y = y := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (map_ne_zero (algebraMap K L)).2 θ.ne_zero (by rw [← hr]; simp)
  obtain ⟨x, hx0, hx⟩ : ∃ x : L, x ≠ 0 ∧ u * σ x = x := by
    by_cases h : 1 + (u : L) = 0
    · exact ⟨r, hr0, by rw [hσ]; linear_combination (-r) * h⟩
    · exact ⟨1 + u, h, by rw [map_add, map_one]; linear_combination hu1⟩
  obtain ⟨a, b, hab⟩ := hb x
  have hσx : σ x = algebraMap K L a - algebraMap K L b * r := by
    rw [hab, map_add, map_mul, hσ, σ.commutes, σ.commutes]; ring
  obtain ⟨c, hc⟩ := hS.gen (a := a) (b := b) (by
    by_contra h
    push Not at h
    simp [h.1, h.2, hx0] at hab)
  have hc0 : algebraMap K L c ≠ 0 := by simp
  refine ⟨Units.mk0 (x / algebraMap K L c) (div_ne_zero hx0 hc0), fun w hw => ?_, ?_⟩
  · have hv := (hT w).not.1 hw
    have h1 : w.valuation L (σ x) = w.valuation L x := by
      conv_rhs => rw [← hx, map_mul, hu w hw, one_mul]
    have h2 : w.valuation L 2 = 1 := by
      have := (val_eq_one w).2 (hS.1 _ hv)
      rwa [map_ofNat] at this
    have h3 : w.valuation L r = 1 := by
      have := (val_eq_one w).2 (hθ _ hv)
      rwa [← hr, map_pow, pow_eq_one_iff_of_nonneg zero_le two_ne_zero] at this
    have h4 : w.valuation L (algebraMap K L c)
        = max (w.valuation L (algebraMap K L a)) (w.valuation L (algebraMap K L b)) := by
      obtain ⟨e, -, h⟩ := val_under (K := K) w
      rw [h, h, h, hc _ hv]
      exact Monotone.map_max (f := fun x : ℤᵐ⁰ => x ^ e) (fun _ _ h => pow_le_pow_left' h e)
    rw [Units.val_mk0, map_div₀, div_eq_one_iff_eq (by simp), h4]
    refine le_antisymm ?_ (max_le ?_ ?_)
    · rw [hab]
      refine (Valuation.map_add _ _ _).trans (le_of_eq ?_)
      rw [map_mul, h3, mul_one]
    · have := Valuation.map_add_le _ le_rfl h1.le
      have h5 : x + σ x = 2 * algebraMap K L a := by rw [hσx]; linear_combination hab
      rwa [h5, map_mul, h2, one_mul] at this
    · have := Valuation.map_sub_le _ le_rfl h1.le
      have h5 : x - σ x = 2 * (algebraMap K L b * r) := by rw [hσx]; linear_combination hab
      rwa [h5, map_mul, map_mul, h2, h3, one_mul, mul_one] at this
  · rw [Units.val_mk0, map_div₀, σ.commutes, ← mul_div_assoc, hx]

private lemma norm_index_count_bound [IsTotallyComplex K] {θ : Kˣ} {r : L} (hr : r ^ 2 = algebraMap K L θ)
    (σ : L ≃ₐ[K] L) (hσ : σ r = -r)
    (hb : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r) (h2 : finrank K L = 2)
    {S P : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (hθ : θ ∈ US S) (hP : P ⊆ S)
    (h : ∀ v ∈ P, θ ∈ Qv (v.valuation K)) :
    (Nm (θ : K)).relIndex (US S) ≠ 0 ∧
      2 ^ (P.card + 1) * (Nm (θ : K)).relIndex (US S) ≤ 2 ^ S.card := by
  obtain ⟨T, hT⟩ := exists_SL L S
  have hcard := card_SL hr σ hσ hP h hT
  have hn0 : ∀ a b : K, (algebraMap K L a + algebraMap K L b * r) *
      σ (algebraMap K L a + algebraMap K L b * r) = algebraMap K L (a ^ 2 - θ * b ^ 2) := by
    intro a b
    rw [map_add, map_mul, hσ, σ.commutes, σ.commutes, map_sub, map_mul, map_pow, map_pow, ← hr]
    ring
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨a, b, rfl⟩ := hb x
    simp [hσ]
  have hn : ∀ x : Lˣ, ∃ y : Kˣ, algebraMap K L y = x * σ x := by
    intro x
    obtain ⟨a, b, hx⟩ := hb x
    have := hn0 a b
    rw [← hx] at this
    exact ⟨Units.mk0 (a ^ 2 - θ * b ^ 2) fun h0 => by simp [h0] at this, this.symm⟩
  choose n hn using hn
  have inj : ∀ {x y : Kˣ}, algebraMap K L x = algebraMap K L y → x = y := fun h =>
    Units.ext ((algebraMap K L).injective h)
  let N : Lˣ →* Kˣ := MonoidHom.mk' n fun x y => inj (by
    rw [Units.val_mul, map_mul, hn, hn, hn, Units.val_mul, map_mul]; ring)
  have hN : ∀ x, algebraMap K L (N x) = x * σ x := hn
  let s : Lˣ →* Lˣ := Units.map (σ : L →* L)
  have hs : ∀ x, (s x : L) = σ x := fun _ => rfl
  let ι : Kˣ →* Lˣ := Units.map (algebraMap K L : K →* L)
  have hι : ∀ x, (ι x : L) = algebraMap K L x := fun _ => rfl
  have hsT : ∀ x ∈ US T, s x ∈ US T := by
    intro x hx w hw
    obtain ⟨w', h1, h2⟩ := exists_conj σ w
    rw [hs, ← h2]
    exact hx w' (by rwa [hT, h1, ← hT])
  have hιT : ∀ x ∈ US S, ι x ∈ US T := fun x hx w hw =>
    (val_eq_one w).2 (hx _ ((hT w).not.1 hw))
  have hNT : ∀ x ∈ US T, N x ∈ US S := by
    intro x hx v hv
    obtain ⟨w, rfl⟩ := exists_over L v
    rw [← val_eq_one, hN]
    exact mul_mem hx (hsT x hx) w ((hT w).not.2 hv)
  let NU : US T →* US S := (N.comp (US T).subtype).codRestrict _ fun x => hNT _ x.2
  let U1 : Subgroup Lˣ := US T ⊓ N.ker
  have hU1 : ∀ x, x ∈ U1 ↔ x ∈ US T ∧ (x : L) * σ x = 1 := by
    intro x
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => inj (by rw [hN, h]; simp)⟩
    rw [← hN, show N x = 1 from h]; simp
  let δ : US T →* U1 := (((MonoidHom.id Lˣ) / s).comp (US T).subtype).codRestrict _ fun x => by
    refine (hU1 _).2 ⟨div_mem x.2 (hsT _ x.2), ?_⟩
    simp [hs, hσσ]
  have hδ : ∀ x, ((δ x : Lˣ) : L) = (x : Lˣ) / σ (x : Lˣ) := fun x => by
    rw [← hs, ← Units.val_div_eq_div_val]; rfl
  have hsurj : Function.Surjective δ := by
    rintro ⟨u, hu⟩
    obtain ⟨y, hy, h1⟩ := exists_unit hr σ hσ hb hS hθ hT ((hU1 u).1 hu).1 ((hU1 u).1 hu).2
    refine ⟨⟨y, hy⟩, Subtype.ext (Units.ext ?_)⟩
    rw [hδ, div_eq_iff (by simp), h1]
  obtain ⟨hfK, hrK⟩ := US_rank S
  obtain ⟨hfL, hrL⟩ := US_rank T
  let j : Additive U1 →ₗ[ℤ] Additive (US T) :=
    (MonoidHom.toAdditive (Subgroup.inclusion inf_le_left)).toIntLinearMap
  have hf1 : Module.Finite ℤ (Additive U1) :=
    Module.Finite.of_injective j (Subgroup.inclusion_injective inf_le_left)
  have hrk := finrank_le_add j (MonoidHom.toAdditive NU).toIntLinearMap (by
    rintro ⟨x, hx⟩ h
    exact ⟨Additive.ofMul ⟨x, hx, congrArg Subtype.val h⟩, rfl⟩)
  have hi1 := index_sq U1 ((hU1 _).2 ⟨neg_one_mem_US T, by simp⟩)
  have hiK := index_sq_US S
  set D := (powMonoidHom (α := US S) 2).range with hD
  have hDR : D ≤ NU.range := by
    rintro _ ⟨c, rfl⟩
    refine ⟨⟨ι c, hιT _ c.2⟩, Subtype.ext (inj ?_)⟩
    refine (hN _).trans ?_
    simp [hι, sq]
  have hcom : D.comap NU ≤ (powMonoidHom (α := U1) 2).range.comap δ := by
    rintro x ⟨c, hc⟩
    have hc : algebraMap K L ((c : Kˣ) : K) ^ 2 = (x : Lˣ) * σ (x : Lˣ) := by
      rw [← hN]
      have := congrArg (fun t : US S => algebraMap K L ((t : Kˣ) : K)) hc
      refine Eq.trans ?_ this
      simp
    have hc0 : algebraMap K L ((c : Kˣ) : K) ≠ 0 := by simp
    have hx0 : σ (x : Lˣ) ≠ 0 := by simp
    refine ⟨⟨x / ι c, (hU1 _).2 ⟨div_mem x.2 (hιT _ c.2), ?_⟩⟩, Subtype.ext (Units.ext ?_)⟩
    · rw [Units.val_div_eq_div_val, hι, map_div₀, σ.commutes, div_mul_div_comm, ← hc, sq,
        div_self (mul_ne_zero hc0 hc0)]
    · rw [hδ]
      show (((x : Lˣ) / ι c : Lˣ) : L) ^ 2 = _
      rw [Units.val_div_eq_div_val, hι, div_pow, hc]
      field_simp
  have hRN : NU.range ≤ (Nm (θ : K)).subgroupOf (US S) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, hx⟩ := hb (x : Lˣ)
    refine ⟨a, b, (algebraMap K L).injective ?_⟩
    rw [← hn0, ← hx]
    exact hN _
  have e1 := Subgroup.relIndex_mul_index hDR
  rw [← Subgroup.index_comap, hiK] at e1
  have e2 := Subgroup.index_dvd_of_le hcom
  rw [Subgroup.index_comap_of_surjective _ hsurj, hi1] at e2
  have e3 := mul_dvd_mul e2 (Subgroup.index_dvd_of_le hRN)
  rw [e1, ← Subgroup.relIndex] at e3
  refine ⟨fun h0 => by simp [h0] at e3, ?_⟩
  have e4 := Nat.le_of_dvd (by positivity) e3
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  have f1 := IsTotallyComplex.finrank K
  have f2 := IsTotallyComplex.finrank L
  have f3 := finrank_mul_finrank ℚ K L
  have f4 := finrank_pos (R := ℚ) (M := K)
  rw [hrK, hrL, Units.rank, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.nrRealPlaces_eq_zero] at hrk
  rw [h2] at f3
  have e5 : 2 ^ (InfinitePlace.nrComplexPlaces K + (P.card + 1)) ≤ 2 ^ (finrank ℤ (Additive U1) + 1) :=
    Nat.pow_le_pow_right two_pos (by omega)
  have e6 := (Nat.mul_le_mul_right _ e5).trans e4
  rw [pow_add, pow_add 2 _ S.card, mul_assoc] at e6
  exact Nat.le_of_mul_le_mul_left e6 (by positivity)

end ct

private lemma exists_quad {K : Type} [Field K] [NumberField K] {θ : K} (h : ¬ IsSquare θ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (r : L) (σ : L ≃ₐ[K] L),
      r ^ 2 = algebraMap K L θ ∧ σ r = -r ∧
      (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r) ∧ finrank K L = 2 := by
  have : Fact (∀ r : K, r ^ 2 ≠ θ + 0 * r) := ⟨fun r hr => h ⟨r, by rw [← sq, hr]; simp⟩⟩
  have : NumberField (QuadraticAlgebra K θ 0) := NumberField.of_module_finite K _
  refine ⟨QuadraticAlgebra K θ 0, inferInstance, this, inferInstance, QuadraticAlgebra.omega,
    { (starRingAut : RingAut (QuadraticAlgebra K θ 0)) with commutes' := ?_ }, ?_, ?_, ?_,
    QuadraticAlgebra.finrank_eq_two _ _⟩
  · intro r; ext <;> simp
  · ext <;> simp [sq]
  · show star _ = _
    ext <;> simp
  · intro x
    exact ⟨x.re, x.im, by ext <;> simp⟩

section glob
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

private lemma count {θ : Kˣ} (hsq : ¬ IsSquare (θ : K))
    {S P : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (hθ : θ ∈ US S) (hP : P ⊆ S)
    (h : ∀ v ∈ P, θ ∈ Qv (v.valuation K)) :
    (Nm (θ : K)).relIndex (US S) ≠ 0 ∧
      2 ^ (P.card + 1) * (Nm (θ : K)).relIndex (US S) ≤ 2 ^ S.card := by
  obtain ⟨L, _, _, _, r, σ, h1, h2, h3, h4⟩ := exists_quad hsq
  exact norm_index_count_bound h1 σ h2 h3 h4 hS hθ hP h

private lemma count_contra {θ : Kˣ} (hsq : ¬ IsSquare (θ : K))
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (hθ : θ ∈ US S)
    (hx : ∀ v ∈ S, θ ∉ Qv (v.valuation K) → ∃ x ∈ US S, x ∉ LN (v.valuation K) θ ∧
      ∀ w ∈ S, θ ∉ Qv (w.valuation K) → w ≠ v → x ∈ LN (w.valuation K) θ) : False := by
  classical
  obtain ⟨h0, h1⟩ := count hsq hS hθ (Finset.filter_subset (fun v => θ ∈ Qv (v.valuation K)) S)
    (fun v hv => by rw [Finset.mem_filter] at hv; exact hv.2)
  have hle : Nm (θ : K) ≤ ⨅ v ∈ S.filter (fun v => θ ∉ Qv (v.valuation K)),
      LN (v.valuation K) θ := le_iInf₂ fun _ _ => le_sup_left
  have h2 := pow_le_relIndex (fun v : HeightOneSpectrum (𝓞 K) => LN (v.valuation K) θ) (US S)
    (S.filter (fun v => θ ∉ Qv (v.valuation K))) (fun v hv => by
      obtain ⟨x, h1, h2, h3⟩ := hx v (Finset.mem_filter.1 hv).1 (Finset.mem_filter.1 hv).2
      exact ⟨x, h1, h2, fun w hw => h3 w (Finset.mem_filter.1 hw).1 (Finset.mem_filter.1 hw).2⟩)
    (ne_zero_of_dvd_ne_zero h0 (Subgroup.relIndex_dvd_of_le_left _ hle))
  have h3 := (Nat.mul_le_mul_left _ (h2.trans (Subgroup.relIndex_le_of_le_left hle h0))).trans h1
  rw [← pow_add, Nat.pow_le_pow_iff_right one_lt_two] at h3
  have := Finset.card_filter_add_card_filter_not (s := S) (fun v => θ ∈ Qv (v.valuation K))
  omega

omit [IsTotallyComplex K] in
private lemma not_LN {v : HeightOneSpectrum (𝓞 K)} {θ : K} {α x : Kˣ}
    (hα : α ∉ LN (v.valuation K) θ) (h : α⁻¹ * x ∈ Qv (v.valuation K)) :
    x ∉ LN (v.valuation K) θ := fun hx => hα (by
  simpa using mul_mem hx (inv_mem (Qv_le_LN _ θ h)))

omit [IsTotallyComplex K] in
private lemma exists_dual {θ : Kˣ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) : ∃ x : Kˣ, (θ ∉ Qv (v.valuation K) → x ∉ LN (v.valuation K) θ) ∧
      ∀ w ∈ S, w ≠ v → x ∈ LN (w.valuation K) θ := by
  by_cases h : θ ∈ Qv (v.valuation K)
  · exact ⟨1, fun h' => absurd h h', fun _ _ _ => one_mem _⟩
  obtain ⟨α, hα⟩ := nonnorm' v h
  obtain ⟨x, h1, h2⟩ := weak_approx v S α
  exact ⟨x, fun _ => not_LN hα h1, fun w hw hwv => Qv_le_LN _ _ (h2 w hw hwv)⟩

private lemma exists_nonsplit {θ : Kˣ} (hsq : ¬ IsSquare (θ : K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ∃ v ∉ S, θ ∉ Qv (v.valuation K) := by
  classical
  by_contra hc
  push Not at hc
  choose x hx hx' using exists_dual (θ := θ) S
  choose T hT using fun v => exists_US (x v)
  obtain ⟨G, hG⟩ := exists_good (K := K)
  obtain ⟨A, hA⟩ := exists_US θ
  have hS : ∀ v, θ ∉ Qv (v.valuation K) → v ∈ S := fun v hv => by_contra fun h => hv (hc v h)
  refine count_contra hsq (S := G ∪ (A ∪ S.biUnion T)) (hG.mono Finset.subset_union_left)
    (US_mono (Finset.subset_union_left.trans Finset.subset_union_right) hA) fun v _ hv => ?_
  refine ⟨x v, US_mono ?_ (hT v), hx v hv, fun w _ hw => hx' v w (hS w hw)⟩
  exact (Finset.subset_biUnion_of_mem T (hS v hv)).trans
    (Finset.subset_union_right.trans Finset.subset_union_right)

private lemma exists_prime {θ u : Kˣ} (hsq : ¬ IsSquare (θ : K)) (hu : ¬ IsSquare (u : K))
    (huθ : ¬ IsSquare (u * θ : K)) {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S)
    (hθS : θ ∈ US S) (huS : u ∈ US S) :
    ∃ v ∉ S, θ ∈ Qv (v.valuation K) ∧ u ∉ Qv (v.valuation K) := by
  obtain ⟨L, _, _, _, r, σ, h1, h2, h3, -⟩ := exists_quad hsq
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  obtain ⟨T, hT⟩ := exists_SL L S
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (map_ne_zero (algebraMap K L)).2 θ.ne_zero (by rw [← h1]; simp)
  obtain ⟨w, hw, h4⟩ := exists_nonsplit (θ := Units.map (algebraMap K L : K →* L) u) (by
    rintro ⟨x, hx⟩
    obtain ⟨a, b, rfl⟩ := h3 x
    have hx : algebraMap K L u = _ := hx
    have h5 := congrArg σ hx
    simp only [map_mul, map_add, h2, σ.commutes] at h5
    have h6 : 4 * algebraMap K L a * algebraMap K L b * r = 0 := by linear_combination h5 - hx
    simp only [mul_eq_zero, map_eq_zero, hr0, or_false] at h6
    rcases h6 with (h6 | rfl) | rfl
    · norm_num at h6
    · refine huθ ⟨b * θ, (algebraMap K L).injective ?_⟩
      simp only [map_mul, hx, ← h1, map_zero]; ring
    · refine hu ⟨a, (algebraMap K L).injective ?_⟩
      simp [hx]) T
  have hv := (hT w).not.1 hw
  have h5 : u ∉ Qv ((w.under (𝓞 K)).valuation K) := fun h => h4 (map_mem_Qv w h)
  refine ⟨_, hv, by_contra fun h6 => h4 ?_, h5⟩
  have h7 := map_mem_Qv w (mul_mem_Qv _ (hS.1 _ hv) (huS _ hv) (hθS _ hv) h5 h6)
  have h8 : Units.map (algebraMap K L : K →* L) θ = Units.mk0 r hr0 ^ 2 := Units.ext h1.symm
  rw [map_mul, h8] at h7
  exact (Subgroup.mul_mem_cancel_right _ (sq_mem_Qv _ _)).1 h7

omit [IsTotallyComplex K] in
private lemma mem_sq {S : Finset (HeightOneSpectrum (𝓞 K))} (u : US S)
    (h : IsSquare ((u : Kˣ) : K)) : u ∈ (powMonoidHom (α := US S) 2).range := by
  obtain ⟨y, hy⟩ := h
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have : Units.mk0 y hy0 ^ 2 = u := Units.ext (by simp [hy, sq])
  exact ⟨⟨Units.mk0 y hy0, root_mem_US (this ▸ u.2)⟩, Subtype.ext this⟩

omit [IsTotallyComplex K] in
private lemma mul_mem_Qv' {v : HeightOneSpectrum (𝓞 K)} (h2 : v.valuation K 2 = 1) {x y : Kˣ}
    (hx : v.valuation K x = 1) (hy : v.valuation K y = 1)
    (h : x ∈ Qv (v.valuation K) ↔ y ∈ Qv (v.valuation K)) : x * y ∈ Qv (v.valuation K) := by
  by_cases h1 : x ∈ Qv (v.valuation K)
  · exact mul_mem h1 (h.1 h1)
  · exact mul_mem_Qv v h2 hx hy h1 (h.not.1 h1)

private lemma exists_strictHenselian_absolutely_closed_local_ring {θ : Kˣ} (hsq : ¬ IsSquare (θ : K))
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S) (hθ : θ ∈ US S) (k : ℕ)
    (hk : k + 1 ≤ InfinitePlace.nrComplexPlaces K + S.card) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), T.card = k ∧ (∀ v ∈ T, v ∉ S) ∧
      (∀ v ∈ T, θ ∈ Qv (v.valuation K)) ∧ ∀ A : HeightOneSpectrum (𝓞 K) → Prop,
        ∃ u ∈ US S, ∀ v ∈ T, (u ∈ Qv (v.valuation K) ↔ A v) := by
  classical
  induction k with
  | zero => exact ⟨∅, rfl, by simp, by simp, fun _ => ⟨1, one_mem _, by simp⟩⟩
  | succ k ih =>
  obtain ⟨T, hT, h1, h2, h3⟩ := ih (by omega)
  have : ∃ u ∈ US S, (∀ v ∈ T, u ∈ Qv (v.valuation K)) ∧ ¬ IsSquare (u : K) ∧
      ¬ IsSquare (u * θ : K) := by
    by_contra hc
    push Not at hc
    set KT := ⨅ v ∈ T, Qv (v.valuation K) with hKT
    have hm : ∀ x, x ∈ KT ↔ ∀ v ∈ T, x ∈ Qv (v.valuation K) := by simp [hKT, Subgroup.mem_iInf]
    have e1 := relIndex_le_card KT (US S)
      (fun x (v : T) => decide ((x : Kˣ) ∈ Qv (v.1.valuation K))) (fun x y h => (hm _).2 fun v hv =>
        mul_mem_Qv' (hS.1 _ (h1 v hv)) (inv_mem x.2 _ (h1 v hv)) (y.2 _ (h1 v hv))
          (by simpa using congrFun h ⟨v, hv⟩))
    have e2 := relIndex_le_card (powMonoidHom (α := US S) 2).range (KT.subgroupOf (US S))
      (fun x => decide (IsSquare (((x : US S) : Kˣ) : K))) (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        refine mem_sq _ ?_
        simp only [decide_eq_decide] at h
        show IsSquare (((x : Kˣ)⁻¹ * y : Kˣ) : K)
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        by_cases hs : IsSquare ((x : Kˣ) : K)
        · exact hs.inv.mul (h.1 hs)
        · have := (hc _ x.2 ((hm _).1 hx) hs).inv.mul (hc _ y.2 ((hm _).1 hy) (h.not.1 hs))
          have e : ((x : Kˣ) : K)⁻¹ * (y : Kˣ) = ((x : Kˣ) * θ : K)⁻¹ * ((y : Kˣ) * θ) := by
            field_simp
          rwa [e])
    have e3 := Subgroup.relIndex_mul_index
      (H := (powMonoidHom (α := US S) 2).range) (K := KT.subgroupOf (US S)) (by
        rintro _ ⟨y, rfl⟩
        exact (hm _).2 fun v _ => sq_mem_Qv _ _)
    have e4 := Nat.mul_le_mul e2.2 e1.2
    rw [Subgroup.relIndex, Subgroup.relIndex] at e4
    rw [Subgroup.relIndex, index_sq_US] at e3
    rw [e3, Nat.card_fun] at e4
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_coe] at e4
    rw [← pow_succ', Nat.pow_le_pow_iff_right one_lt_two] at e4
    omega
  obtain ⟨u, hu, hu1, hu2, hu3⟩ := this
  obtain ⟨v, hv, hv1, hv2⟩ := exists_prime hsq hu2 hu3 hS hθ hu
  have hvT : v ∉ T := fun h => hv2 (hu1 v h)
  refine ⟨insert v T, by rw [Finset.card_insert_of_notMem hvT, hT], ?_, ?_, fun A => ?_⟩
  · simpa [hv] using h1
  · simpa [hv1] using h2
  · obtain ⟨x, hx, hx1⟩ := h3 A
    by_cases h : x ∈ Qv (v.valuation K) ↔ A v
    · exact ⟨x, hx, by simpa [h] using hx1⟩
    · refine ⟨x * u, mul_mem hx hu, ?_⟩
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · by_cases h' : x ∈ Qv (w.valuation K)
        · rw [Subgroup.mul_mem_cancel_left _ h']; tauto
        · have := mul_mem_Qv w (hS.1 _ hv) (hx _ hv) (hu _ hv) h' hv2
          tauto
      · rw [Subgroup.mul_mem_cancel_right _ (hu1 w hw)]
        exact hx1 w hw

private lemma isSquare_of [DecidableEq (HeightOneSpectrum (𝓞 K))]
    {S T : Finset (HeightOneSpectrum (𝓞 K))} (hS : Good S)
    (h1 : ∀ v ∈ T, v ∉ S) (h3 : ∀ A : HeightOneSpectrum (𝓞 K) → Prop,
        ∃ u ∈ US S, ∀ v ∈ T, (u ∈ Qv (v.valuation K) ↔ A v))
    {b : Kˣ} (hb : b ∈ US (S ∪ T)) (hb' : ∀ v ∈ S, b ∈ Qv (v.valuation K)) :
    IsSquare (b : K) := by
  by_contra hsq
  refine count_contra hsq (hS.mono Finset.subset_union_left) hb fun v hv hvb => ?_
  have hT : ∀ v ∈ S ∪ T, b ∉ Qv (v.valuation K) → v ∈ T := fun v hv hvb =>
    (Finset.mem_union.1 hv).resolve_left fun h => hvb (hb' v h)
  have hvT := hT v hv hvb
  have hvS := h1 v hvT
  obtain ⟨α, hα⟩ := nonnorm' v hvb
  obtain ⟨c, hc, hc'⟩ := hS.single hvS α
  obtain ⟨u, hu, hu'⟩ := h3 fun w => (if w = v then α⁻¹ * c else c) ∈ Qv (w.valuation K)
  refine ⟨c * u, mul_mem ?_ (US_mono Finset.subset_union_left hu), not_LN hα ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_union, not_or] at hw
    exact hc' w hw.1 fun h => hw.2 (h ▸ hvT)
  · rw [← mul_assoc]
    exact mul_mem_Qv' (hS.1 _ hvS) (by simp [hc]) (hu _ hvS) (by simpa using (hu' v hvT).symm)
  · intro w hw hwb hwv
    have hwT := hT w hw hwb
    have hwS := h1 w hwT
    exact Qv_le_LN _ _ (mul_mem_Qv' (hS.1 _ hwS) (hc' w hwS hwv) (hu _ hwS)
      (by simpa [hwv] using (hu' w hwT).symm))

private lemma hasse {θ ε : Kˣ} (h : ∀ v : HeightOneSpectrum (𝓞 K), ε ∈ LN (v.valuation K) θ) :
    ε ∈ Nm (θ : K) := by
  classical
  by_cases hsq : IsSquare (θ : K)
  · obtain ⟨t, ht⟩ := hsq
    have : t ≠ 0 := by rintro rfl; simp at ht
    refine ⟨(ε + 1) / 2, (ε - 1) / (2 * t), ?_⟩
    rw [ht]; field_simp; ring
  obtain ⟨G, hG⟩ := exists_good (K := K)
  obtain ⟨A, hA⟩ := exists_US θ
  obtain ⟨B, hB⟩ := exists_US ε
  obtain ⟨S, hS, hθ, hε⟩ : ∃ S, Good S ∧ θ ∈ US S ∧ ε ∈ US S :=
    ⟨G ∪ (A ∪ B), hG.mono Finset.subset_union_left,
      US_mono (Finset.subset_union_left.trans Finset.subset_union_right) hA,
      US_mono (Finset.subset_union_right.trans Finset.subset_union_right) hB⟩
  have f1 := IsTotallyComplex.finrank K
  have f4 := finrank_pos (R := ℚ) (M := K)
  obtain ⟨T, hT, h1, h2, h3⟩ :=
    exists_strictHenselian_absolutely_closed_local_ring hsq hS hθ (InfinitePlace.nrComplexPlaces K + S.card - 1) (by omega)
  have hcard : (S ∪ T).card = S.card + T.card :=
    Finset.card_union_of_disjoint (Finset.disjoint_right.2 h1)
  set U := US (S ∪ T) with hU
  set I := S.filter (fun v => θ ∉ Qv (v.valuation K)) with hI
  set Λ := ⨅ v ∈ I, LN (v.valuation K) θ with hΛ
  obtain ⟨q0, q1⟩ := index_QS S
  set QS := ⨅ v ∈ S, Qv (v.valuation K) with hQS
  have hQΛ : QS ≤ Λ := le_iInf₂ fun v hv =>
    (iInf₂_le v (Finset.mem_filter.1 hv).1).trans (Qv_le_LN _ _)
  have split : ∀ H : Subgroup Kˣ, H.relIndex U * (H ⊔ U).index = H.index := fun H => by
    rw [← Subgroup.relIndex_sup_left, Subgroup.relIndex_mul_index le_sup_left]
  have e1 := split QS
  have e2 := split Λ
  have e3 : QS.subgroupOf U ≤ (powMonoidHom (α := U) 2).range := fun x hx =>
    mem_sq x (isSquare_of hS h1 h3 x.2 fun v hv => (iInf₂_le v hv : QS ≤ _) hx)
  have e4 := Nat.le_of_dvd (Nat.pos_of_ne_zero (left_ne_zero_of_mul (e1 ▸ q0)))
    (Subgroup.index_dvd_of_le e3)
  rw [index_sq_US, hcard] at e4
  have e5 : (QS ⊔ U).index ≤ 2 := by
    have := (Nat.mul_le_mul_right _ e4).trans (e1.le.trans q1)
    have h5 : 4 ^ S.card * 2 ^ finrank ℚ K
        = 2 ^ (InfinitePlace.nrComplexPlaces K + (S.card + T.card)) * 2 := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_succ]
      congr 1
      omega
    rw [h5] at this
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have e6 : (Λ ⊔ U).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (right_ne_zero_of_mul (e1 ▸ q0)))
      (Subgroup.index_dvd_of_le (sup_le_sup_right hQΛ U))).trans e5
  have e7 := pow_le_relIndex (fun v : HeightOneSpectrum (𝓞 K) => LN (v.valuation K) θ) ⊤ I
    (fun v hv => by
      obtain ⟨x, h1, h2⟩ := exists_dual (θ := θ) I v
      exact ⟨x, trivial, h1 (Finset.mem_filter.1 hv).2, h2⟩)
    (by
      rw [Subgroup.relIndex_top_right]
      exact ne_zero_of_dvd_ne_zero q0 (Subgroup.index_dvd_of_le hQΛ))
  rw [Subgroup.relIndex_top_right, ← hΛ, ← e2] at e7
  obtain ⟨e8, e9⟩ := count hsq (P := S.filter (fun v => θ ∈ Qv (v.valuation K)) ∪ T)
    (hS.mono Finset.subset_union_left) (US_mono Finset.subset_union_left hθ)
    (Finset.union_subset_union_left (Finset.filter_subset _ _)) (fun v hv => by
      rcases Finset.mem_union.1 hv with h | h
      · exact (Finset.mem_filter.1 h).2
      · exact h2 v h)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_right.2 fun v hv h =>
    h1 v hv (Finset.mem_filter.1 h).1), hcard, ← hU] at e9
  have hc := Finset.card_filter_add_card_filter_not (s := S) (fun v => θ ∈ Qv (v.valuation K))
  rw [← hI] at hc
  have e10 : 2 * (Nm (θ : K)).relIndex U ≤ 2 ^ I.card := by
    have h5 : S.card + T.card
      = (S.filter (fun v => θ ∈ Qv (v.valuation K))).card + T.card + I.card := by omega
    rw [h5, pow_succ, pow_add 2 _ I.card, mul_assoc] at e9
    exact Nat.le_of_mul_le_mul_left e9 (by positivity)
  have hle : Nm (θ : K) ≤ Λ := le_iInf₂ fun _ _ => le_sup_left
  have e11 := Subgroup.relIndex_inf_mul_relIndex (Nm (θ : K)) Λ U
  rw [inf_eq_left.2 hle] at e11
  rw [← hU] at e8
  have e12 : (Nm (θ : K)).relIndex (Λ ⊓ U) = 1 := by
    have a1 := e7.trans (Nat.mul_le_mul_left _ e6)
    have a2 := left_ne_zero_of_mul (e11 ▸ e8)
    have a3 := right_ne_zero_of_mul (e11 ▸ e8)
    have a4 : (Nm (θ : K)).relIndex (Λ ⊓ U) * Λ.relIndex U ≤ 1 * Λ.relIndex U := by omega
    have := Nat.le_of_mul_le_mul_right a4 (Nat.pos_of_ne_zero a3)
    omega
  refine Subgroup.relIndex_eq_one.1 e12 ⟨?_, US_mono Finset.subset_union_left hε⟩
  exact Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun _ => h v

end glob

private lemma powerSeries_expansion_image_dense_with_denominator {F A : Type*} [Field F] [Field A] [Valued A ℤᵐ⁰] (f : F →+* A)
    (hf : DenseRange f) {Δ : F} (c : F) (a b : A) (h : -1 = a ^ 2 - f Δ * b ^ 2) :
    ∃ x y : F, Valued.v (f ((x ^ 2 - Δ * y ^ 2 + 1) * c)) ≤ 1 := by
  have hc : Continuous fun p : A × A => (p.1 ^ 2 - f Δ * p.2 ^ 2 + 1) * f c := by fun_prop
  obtain ⟨⟨x, y⟩, hxy⟩ := (hf.prodMap hf).exists_mem_open
    ((Valued.isOpen_valuationSubring A).preimage hc) ⟨(a, b), by simp [← h]⟩
  refine ⟨x, y, ?_⟩
  rw [map_mul f, map_add f, map_sub f, map_mul f, map_pow f, map_pow f, map_one f]
  exact hxy

private lemma local_norm {F : Type} [Field F] [NumberField F] {Δ : F}
    (v : HeightOneSpectrum (𝓞 F)) (a b : v.adicCompletion F)
    (h : -1 = a ^ 2 - algebraMap F _ Δ * b ^ 2) :
    ∃ a b : F, v.valuation F (a ^ 2 - Δ * b ^ 2 + 1) < v.valuation F 4 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : v.valuation F π ≠ 0 := by rw [hπ]; exact WithZero.exp_ne_zero
  have hπ1 : v.valuation F π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨x, y, h1⟩ := powerSeries_expansion_image_dense_with_denominator (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap F)
    (4 * π)⁻¹ a b h
  refine ⟨x, y, ?_⟩
  have h2 : v.valuation F ((x ^ 2 - Δ * y ^ 2 + 1) * (4 * π)⁻¹) ≤ 1 := by
    rw [← HeightOneSpectrum.adicCompletion.valued_coe F v]
    exact h1
  have h4 := zero_lt_iff.2 (v_four_ne (v.valuation F))
  rw [← div_eq_mul_inv, map_div₀, map_mul, div_le_one₀ (mul_pos h4 (zero_lt_iff.2 hπ0))] at h2
  exact h2.trans_lt (mul_lt_of_lt_one_right h4 hπ1)

private lemma main {F : Type} [Field F] [NumberField F] {Δ d : F} (hΔ : Δ ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ a b : F, v.valuation F (a ^ 2 - Δ * b ^ 2 + 1) < v.valuation F 4)
    (σ₀ : F →+* ℝ) (hd : ∀ σ : F →+* ℝ, σ d < 0) :
    ∃ p₀ p₁ q₀ q₁ : F, p₀ ^ 2 + d * p₁ ^ 2 - Δ * (q₀ ^ 2 + d * q₁ ^ 2) = -1 ∧
      p₀ * p₁ = Δ * q₀ * q₁ := by
  have hsq : ¬ IsSquare d := by
    rintro ⟨t, rfl⟩
    exact absurd (hd σ₀) (not_lt.2 (by rw [map_mul]; exact mul_self_nonneg _))
  obtain ⟨E, _, _, _, r, σ, h1, h2, h3, -⟩ := exists_quad hsq
  have : IsTotallyComplex E := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by
    have := hd ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F E))
    rw [RingHom.comp_apply, ← h1, map_pow] at this
    exact absurd this (not_lt.2 (sq_nonneg _))⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    refine hsq ⟨0, (algebraMap F E).injective ?_⟩
    rw [← h1]; simp
  obtain ⟨p, q, hpq⟩ := hasse (K := E) (θ := Units.mk0 (algebraMap F E Δ) (by simpa using hΔ))
    (ε := -1) fun w => by
      obtain ⟨a, b, hab⟩ := h (w.under (𝓞 F))
      have h4 := (val_lt w).2 hab
      rw [map_ofNat, map_add, map_one] at h4
      set n := algebraMap F E (a ^ 2 - Δ * b ^ 2) with hn
      have h5 : w.valuation E (-n - 1) < w.valuation E 4 := by
        rwa [← Valuation.map_neg, neg_sub, sub_neg_eq_add, add_comm]
      have hn0 : -n ≠ 0 := by
        intro h0
        have := v_eq_one _ (h5.trans_le (v_four _))
        simp [h0] at this
      have h6 : Units.mk0 _ hn0 ∈ near4 (w.valuation E) := h5
      refine Subgroup.mem_sup.2 ⟨-Units.mk0 _ hn0, ⟨algebraMap F E a, algebraMap F E b, ?_⟩, _,
        inv_mem h6, by simp⟩
      simp [hn]
  obtain ⟨p₀, p₁, rfl⟩ := h3 p
  obtain ⟨q₀, q₁, rfl⟩ := h3 q
  simp only [Units.val_neg, Units.val_one, Units.val_mk0] at hpq
  have h7 := congrArg σ hpq
  simp only [map_neg, map_one, map_sub, map_mul, map_add, map_pow, h2, σ.commutes] at h7
  refine ⟨p₀, p₁, q₀, q₁, (algebraMap F E).injective ?_, (algebraMap F E).injective ?_⟩
  · simp only [map_neg, map_one, map_sub, map_mul, map_add, map_pow, ← h1]
    linear_combination (-1 / 2) * hpq + (-1 / 2) * h7
  · simp only [map_mul]
    refine mul_right_cancel₀ hr0 ?_
    linear_combination (-1 / 4) * hpq + (1 / 4) * h7

end UpperTheory.Reformulated.B.NormIndexQuadratic

end aux

theorem UpperTheory.Reformulated.B.NormIndexQuadratic.glob_neg_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {Δ d : F},
      Δ ≠ (0 : F) →
        (∀ (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F),
            ∃ (a : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) (b : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v),
              (-1 : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) =
                a ^ (2 : ℕ) - (UpperTheory.Reformulated.B.NormIndexQuadratic.cv v : F → UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) Δ * b ^ (2 : ℕ)) →
          ∀ (σ₀ : F →+* ℝ),
            (∀ (σ : F →+* ℝ), (σ : F → ℝ) d < (0 : ℝ)) →
              ∃ (p₀ : F) (p₁ : F) (q₀ : F) (q₁ : F),
                p₀ ^ (2 : ℕ) + d * p₁ ^ (2 : ℕ) - Δ * (q₀ ^ (2 : ℕ) + d * q₁ ^ (2 : ℕ)) = (-1 : F) ∧ p₀ * p₁ = Δ * q₀ * q₁ := by
  intro F _ _ Δ d hΔ h σ₀ hd
  refine UpperTheory.Reformulated.B.NormIndexQuadratic.main hΔ (fun v => ?_) σ₀ hd
  obtain ⟨a, b, hab⟩ := h v
  exact UpperTheory.Reformulated.B.NormIndexQuadratic.local_norm v a b hab
