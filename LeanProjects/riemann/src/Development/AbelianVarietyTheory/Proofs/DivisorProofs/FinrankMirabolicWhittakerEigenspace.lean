import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.FinGL.Mir

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Abstract

variable {G V F : Type} [Group G] [AddCommGroup V] [Module ℂ V] [Field F]

theorem mem_eig (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ) (v : V) :
    v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr (τ : Representation ℂ G V) {S S' : Set G} {χ χ' : G → ℂ} (hS : ∀ g, g ∈ S ↔ g ∈ S')
    (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S' χ' := by
  ext v
  rw [mem_eig, mem_eig]
  constructor
  · intro hv g hg
    rw [hv g ((hS g).2 hg), h g ((hS g).2 hg)]
  · intro hv g hg
    rw [hv g ((hS g).1 hg), h g hg]

theorem finrank_eig_conj_le [FiniteDimensional ℂ V] (τ : Representation ℂ G V) {S S' : Set G} {χ χ' : G → ℂ} (g : G)
    (h : ∀ s ∈ S', g⁻¹ * s * g ∈ S ∧ χ (g⁻¹ * s * g) = χ' s) :
    finrank ℂ (eig τ S χ) ≤ finrank ℂ (eig τ S' χ') := by
  have hinj : Function.Injective (τ g) := by
    intro x y hxy
    have := congrArg (τ g⁻¹) hxy
    simpa using this
  rw [(Submodule.equivMapOfInjective (τ g) hinj (eig τ S χ)).finrank_eq]
  refine Submodule.finrank_mono ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_eig]
  intro s hs
  have h1 := (mem_eig τ S χ v).1 hv _ (h s hs).1
  have h2 : τ s (τ g v) = τ g (τ (g⁻¹ * s * g) v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h2, h1, (h s hs).2, map_smul]

theorem card_mul_finrank_eig [FiniteDimensional ℂ V] [Finite G] (τ : Representation ℂ G V) (ψ : AddChar F ℂ)
    (K : Subgroup G) [Fintype K] (f : G → F) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x + f y) :
    (Fintype.card K : ℂ) * finrank ℂ (eig τ K fun g => ψ (f g)) =
      ∑ k : K, ψ (-f k) * LinearMap.trace ℂ V (τ k) := by
  have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set e : V →ₗ[ℂ] V := (Fintype.card K : ℂ)⁻¹ • ∑ k : K, ψ (-f k) • τ k with he
  have hp : LinearMap.IsProj (eig τ K fun g => ψ (f g)) e := by
    constructor
    · intro v
      rw [mem_eig]
      intro g hg
      simp only [he, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      rw [smul_comm]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : K)) _ _ fun k => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
      rw [hf g hg k k.2, smul_smul, ← AddChar.map_add_eq_mul, map_mul, Module.End.mul_apply]
      congr 2
      ring
    · intro v hv
      rw [mem_eig] at hv
      simp only [he, LinearMap.smul_apply, LinearMap.sum_apply]
      rw [Finset.sum_congr rfl (g := fun _ => v) fun k _ => by
        rw [hv k k.2, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [← hp.trace, he, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

theorem finrank_eig_fourier [FiniteDimensional ℂ V] [Finite G] [Fintype F] (τ : Representation ℂ G V) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) (K C : Subgroup G) (f l : G → F) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x + f y)
    (hl : ∀ x ∈ K, ∀ y ∈ K, l (x * y) = l x + l y) (hs : ∀ t, ∃ x ∈ K, l x = t) (hC : ∀ x, x ∈ C ↔ x ∈ K ∧ l x = 0) :
    finrank ℂ (eig τ C fun g => ψ (f g)) = ∑ c : F, finrank ℂ (eig τ K fun g => ψ (f g + c * l g)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype C := Fintype.ofFinite C
  have hK : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let φ : K →* Multiplicative F := MonoidHom.mk' (fun k => Multiplicative.ofAdd (l k)) fun x y => by
    rw [← ofAdd_add, Subgroup.coe_mul, hl _ x.2 _ y.2]
  have hφ : φ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro t
    obtain ⟨x, hx, e⟩ := hs t.toAdd
    exact ⟨⟨x, hx⟩, by show Multiplicative.ofAdd (l x) = t; rw [e]; rfl⟩
  let ε : C ≃ {k : K // l k = 0} :=
    { toFun := fun c => ⟨⟨c, ((hC c).1 c.2).1⟩, ((hC c).1 c.2).2⟩
      invFun := fun k => ⟨k.1, (hC _).2 ⟨k.1.2, k.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card K = Fintype.card C * Fintype.card F := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hφ, Subgroup.card_top, Nat.card_eq_fintype_card (α := K),
      Nat.card_eq_fintype_card (α := Multiplicative F), Fintype.card_multiplicative] at h1
    rw [← h1, ← Nat.card_eq_fintype_card (α := C)]
    congr 1
    exact (Nat.card_congr ε).symm
  have h0 := card_mul_finrank_eig τ ψ C f fun x hx y hy => hf x ((hC x).1 hx).1 y ((hC y).1 hy).1
  have h1 : ∀ c : F, _ := fun c => card_mul_finrank_eig τ ψ K (fun g => f g + c * l g) fun x hx y hy => by
    simp only [hf x hx y hy, hl x hx y hy]; ring
  have h2 : (Fintype.card K : ℂ) * finrank ℂ (eig τ C fun g => ψ (f g)) =
      (Fintype.card K : ℂ) * ∑ c : F, (finrank ℂ (eig τ K fun g => ψ (f g + c * l g)) : ℂ) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm, hcard, Nat.cast_mul, mul_right_comm, h0]
    have h3 : ∀ k : K, ∑ c : F, ψ (-(f k + c * l k)) * LinearMap.trace ℂ V (τ k) =
        if l k = 0 then ψ (-f k) * LinearMap.trace ℂ V (τ k) * Fintype.card F else 0 := by
      intro k
      have h4 := AddChar.sum_mulShift (-l k) (AddChar.IsPrimitive.of_ne_one hψ)
      have h5 : ∀ c : F, ψ (-(f k + c * l k)) * LinearMap.trace ℂ V (τ k) =
          ψ (-f k) * LinearMap.trace ℂ V (τ k) * ψ (c * -l k) := by
        intro c
        rw [mul_right_comm, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      rw [Finset.sum_congr rfl fun c _ => h5 c, ← Finset.mul_sum, h4]
      by_cases h : l k = 0 <;> simp [h]
    rw [Finset.sum_congr rfl fun k _ => h3 k, ← Finset.sum_filter,
      Finset.sum_subtype (p := fun k : K => l k = 0) _ (by simp), Finset.sum_mul]
    exact Fintype.sum_equiv ε _ _ fun c => rfl
  exact_mod_cast mul_left_cancel₀ hK h2

theorem finrank_eig_half [FiniteDimensional ℂ V] [Finite G] [Fintype F] (τ : Representation ℂ G V) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) (K C : Subgroup G) (f l : G → F) (hf : ∀ x ∈ K, ∀ y ∈ K, f (x * y) = f x + f y)
    (hl : ∀ x ∈ K, ∀ y ∈ K, l (x * y) = l x + l y) (hs : ∀ t, ∃ x ∈ K, l x = t) (hC : ∀ x, x ∈ C ↔ x ∈ K ∧ l x = 0)
    (hy : ∀ t, ∃ y : G, ∀ u ∈ K, y⁻¹ * u * y ∈ K ∧ l (y⁻¹ * u * y) = l u ∧ f (y⁻¹ * u * y) = f u + t * l u) :
    finrank ℂ (eig τ C fun g => ψ (f g)) = Fintype.card F * finrank ℂ (eig τ K fun g => ψ (f g)) := by
  have h1 : ∀ s s' : F, finrank ℂ (eig τ K fun g => ψ (f g + s * l g)) ≤
      finrank ℂ (eig τ K fun g => ψ (f g + s' * l g)) := by
    intro s s'
    obtain ⟨y, hy⟩ := hy (s' - s)
    refine finrank_eig_conj_le τ y fun u hu => ⟨(hy u hu).1, ?_⟩
    rw [(hy u hu).2.1, (hy u hu).2.2]
    congr 1
    ring
  rw [finrank_eig_fourier τ hψ K C f l hf hl hs hC,
    Finset.sum_congr rfl fun c _ => le_antisymm (h1 c 0) (h1 0 c),
    show (fun g => ψ (f g + 0 * l g)) = fun g => ψ (f g) by simp]
  simp

theorem finrank_eig_exchange [FiniteDimensional ℂ V] [Finite G] [Fintype F] (τ : Representation ℂ G V) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) (D K K' : Subgroup G) (f l m : G → F) (hf : ∀ x ∈ D, ∀ y ∈ D, f (x * y) = f x + f y + l x * m y)
    (hl : ∀ x ∈ D, ∀ y ∈ D, l (x * y) = l x + l y) (hm : ∀ x ∈ D, ∀ y ∈ D, m (x * y) = m x + m y)
    (hK : ∀ x, x ∈ K ↔ x ∈ D ∧ m x = 0) (hK' : ∀ x, x ∈ K' ↔ x ∈ D ∧ l x = 0)
    (hs : ∀ t, ∃ x ∈ K, l x = t) (hs' : ∀ t, ∃ x ∈ K', m x = t) :
    finrank ℂ (eig τ K fun g => ψ (f g)) = finrank ℂ (eig τ K' fun g => ψ (f g)) := by
  have hconj : ∀ φ : G → F, (∀ x ∈ D, ∀ y ∈ D, φ (x * y) = φ x + φ y) → ∀ y ∈ D, ∀ u ∈ D, φ (y⁻¹ * u * y) = φ u := by
    intro φ h y hy u hu
    have h1 := h y hy _ (D.mul_mem (D.mul_mem (D.inv_mem hy) hu) hy)
    rw [show y * (y⁻¹ * u * y) = u * y by group, h u hu y hy] at h1
    linear_combination -h1
  have hfc : ∀ y ∈ D, ∀ u ∈ D, f (y⁻¹ * u * y) = f u + l u * m y - l y * m u := by
    intro y hy u hu
    have h1 := hf y hy _ (D.mul_mem (D.mul_mem (D.inv_mem hy) hu) hy)
    rw [show y * (y⁻¹ * u * y) = u * y by group, hf u hu y hy, hconj m hm y hy u hu] at h1
    linear_combination -h1
  have e1 := finrank_eig_half τ hψ K (K ⊓ K') f l
    (fun x hx y hy => by rw [hf x ((hK x).1 hx).1 y ((hK y).1 hy).1, ((hK y).1 hy).2, mul_zero, add_zero])
    (fun x hx y hy => hl x ((hK x).1 hx).1 y ((hK y).1 hy).1) hs
    (fun x => by rw [Subgroup.mem_inf, hK, hK']; tauto)
    (fun t => by
      obtain ⟨y, hy, e⟩ := hs' t
      obtain ⟨hy, hy0⟩ := (hK' y).1 hy
      refine ⟨y, fun u hu => ?_⟩
      obtain ⟨hu, hu0⟩ := (hK u).1 hu
      refine ⟨(hK _).2 ⟨D.mul_mem (D.mul_mem (D.inv_mem hy) hu) hy, by rw [hconj m hm y hy u hu, hu0]⟩,
        hconj l hl y hy u hu, ?_⟩
      rw [hfc y hy u hu, hu0, e]; ring)
  have e2 := finrank_eig_half τ hψ K' (K ⊓ K') f m
    (fun x hx y hy => by rw [hf x ((hK' x).1 hx).1 y ((hK' y).1 hy).1, ((hK' x).1 hx).2, zero_mul, add_zero])
    (fun x hx y hy => hm x ((hK' x).1 hx).1 y ((hK' y).1 hy).1) hs'
    (fun x => by rw [Subgroup.mem_inf, hK, hK']; tauto)
    (fun t => by
      obtain ⟨y, hy, e⟩ := hs (-t)
      obtain ⟨hy, hy0⟩ := (hK y).1 hy
      refine ⟨y, fun u hu => ?_⟩
      obtain ⟨hu, hu0⟩ := (hK' u).1 hu
      refine ⟨(hK' _).2 ⟨D.mul_mem (D.mul_mem (D.inv_mem hy) hu) hy, by rw [hconj l hl y hy u hu, hu0]⟩,
        hconj m hm y hy u hu, ?_⟩
      rw [hfc y hy u hu, hu0, e]; ring)
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos (e1.symm.trans e2)

end Abstract

theorem solve_rec (q : ℕ) (hq : 1 ≤ q) (k : ℕ) (W D : ℕ → ℕ)
    (h : ∀ m ≤ k, W m = D m + (q - 1) * ∑ a ∈ Finset.range m, W a) :
    ∀ m ≤ k, W m = ∑ j ∈ Finset.range (m + 1), gam q (m - j) * D j := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hg : ∀ l, gam (p + 1) (l + 1) = p * (p + 1) ^ l := by
    intro l
    simp only [gam, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, pow_succ, mul_add, mul_one]
    ring
  have key : ∀ m ≤ k + 1, ∑ a ∈ Finset.range m, W a = ∑ j ∈ Finset.range m, (p + 1) ^ (m - 1 - j) * D j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h m (by omega), ih (by omega), Nat.add_sub_cancel,
        Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, add_comm (D m), ← add_assoc, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show m - j = m - 1 - j + 1 by omega, pow_succ]
      ring
  intro m hm
  rw [h m hm, key m (by omega), Finset.sum_range_succ, Nat.sub_self, Nat.add_sub_cancel, Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show m - j = m - 1 - j + 1 by omega, hg]
    ring
  · simp [gam]

section Concrete

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

def pat (F : Type) [Field F] [Fintype F] (n a e e' m : ℕ) : Subgroup (GL (Fin n) F) :=
  let M : Submonoid (GL (Fin n) F) :=
    { carrier := {u | u ∈ unip F n ∧ ∀ i j : Fin n, i < j → (i.val = a ∧ j.val < e) ∨ (e' ≤ i.val ∧ j.val = m) →
        (u : Matrix (Fin n) (Fin n) F) i j = 0}
      one_mem' := ⟨Subgroup.one_mem _, fun i j h _ => by simp [ne_of_lt h]⟩
      mul_mem' := by
        rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
        refine ⟨Subgroup.mul_mem _ hx hy, fun i j h hz => ?_⟩
        rw [unip_mul_entry hx hy h, hx0 i j h hz, hy0 i j h hz, add_zero]
        intro l h1 h2
        rcases hz with hz | hz
        · rw [hx0 i l h1 (Or.inl ⟨hz.1, by omega⟩), zero_mul]
        · rw [hy0 l j h2 (Or.inr ⟨by omega, hz.2⟩), mul_zero] }
  { M with
    inv_mem' := fun {x} hx => by
      classical
      exact (Submonoid.powers_le.2 (show x ∈ M from hx))
        (mem_powers_iff_mem_zpowers.2 (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))) }

theorem mem_pat {a e e' m : ℕ} {u : GL (Fin n) F} : u ∈ pat F n a e e' m ↔ u ∈ unip F n ∧
    ∀ i j : Fin n, i < j → (i.val = a ∧ j.val < e) ∨ (e' ≤ i.val ∧ j.val = m) →
      (u : Matrix (Fin n) (Fin n) F) i j = 0 := Iff.rfl

omit [Fintype F] in
theorem mem_unip {u : GL (Fin n) F} : u ∈ unip F n ↔ (∀ i j : Fin n, j < i → (u : Matrix (Fin n) (Fin n) F) i j = 0) ∧
    ∀ i, (u : Matrix (Fin n) (Fin n) F) i i = 1 := Iff.rfl

omit [Fintype F] in
theorem unip_mul_entry_exc {x y : GL (Fin n) F} (hx : x ∈ unip F n) (hy : y ∈ unip F n) {i e j : Fin n} (hie : i < e)
    (hej : e < j) (hmid : ∀ l, i < l → l < j → l ≠ e →
      (x : Matrix (Fin n) (Fin n) F) i l * (y : Matrix (Fin n) (Fin n) F) l j = 0) :
    ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (x : Matrix (Fin n) (Fin n) F) i j + (y : Matrix (Fin n) (Fin n) F) i j +
        (x : Matrix (Fin n) (Fin n) F) i e * (y : Matrix (Fin n) (Fin n) F) e j := by
  rw [Units.val_mul, Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ {i, e, j}),
    Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega), unip_diag hx, unip_diag hy]
  · ring
  · intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rcases lt_or_gt_of_ne hl.1 with h | h
    · rw [unip_lower hx h, zero_mul]
    · rcases lt_or_gt_of_ne hl.2.2 with h' | h'
      · exact hmid l h h' hl.2.1
      · rw [unip_lower hy h', mul_zero]

omit [Fintype F] in
theorem edgeSum_mul (Ed : Fin n → Fin n → Prop) [DecidableRel Ed] (hE : ∀ i j, Ed i j → j.val = i.val + 1)
    {x y : GL (Fin n) F} (hx : x ∈ unip F n) (hy : y ∈ unip F n) :
    edgeSum Ed (x * y) = edgeSum Ed x + edgeSum Ed y := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · have := hE i j h
    exact unip_mul_entry hx hy (by omega) fun l h1 h2 => by omega
  · rw [add_zero]

omit [Fintype F] in
theorem edgeSum_congr (Ed Ed' : Fin n → Fin n → Prop) [DecidableRel Ed] [DecidableRel Ed'] (σ : Equiv.Perm (Fin n))
    {x y : GL (Fin n) F}
    (h : ∀ i j, (Ed i j ∧ Ed' (σ i) (σ j) ∧
        (x : Matrix (Fin n) (Fin n) F) i j = (y : Matrix (Fin n) (Fin n) F) (σ i) (σ j)) ∨ (¬ Ed i j ∧ ¬ Ed' (σ i) (σ j)) ∨
      ((x : Matrix (Fin n) (Fin n) F) i j = 0 ∧ (y : Matrix (Fin n) (Fin n) F) (σ i) (σ j) = 0)) :
    edgeSum Ed x = edgeSum Ed' y := by
  unfold edgeSum
  refine Fintype.sum_equiv σ _ _ fun i => Fintype.sum_equiv σ _ _ fun j => ?_
  rcases h i j with h | h | h
  · rw [if_pos h.1, if_pos h.2.1, h.2.2]
  · rw [if_neg h.1, if_neg h.2]
  · rw [h.1, h.2, ite_self, ite_self]

omit [Fintype F] in
theorem edgeSum_add (Ed Ed' : Fin n → Fin n → Prop) [DecidableRel Ed] [DecidableRel Ed'] (a m : Fin n) (h0 : ¬ Ed a m)
    (h : ∀ i j, Ed' i j ↔ Ed i j ∨ (i = a ∧ j = m)) (x : GL (Fin n) F) :
    edgeSum Ed x + (x : Matrix (Fin n) (Fin n) F) a m = edgeSum Ed' x := by
  have h1 : (x : Matrix (Fin n) (Fin n) F) a m =
      ∑ i, ∑ j, if i = a ∧ j = m then (x : Matrix (Fin n) (Fin n) F) i j else 0 := by
    simp [ite_and]
  unfold edgeSum
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h2 : i = a ∧ j = m
  · obtain ⟨rfl, rfl⟩ := h2
    simp [h0, h]
  · simp [h2, h]

theorem exists_transv {a e e' m : ℕ} {s t : Fin n} (hst : s < t)
    (hz : ¬ ((s.val = a ∧ t.val < e) ∨ (e' ≤ s.val ∧ t.val = m))) (c : F) :
    ∃ u ∈ pat F n a e e' m, (u : Matrix (Fin n) (Fin n) F) s t = c := by
  have hne : s ≠ t := ne_of_lt hst
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection s t c)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero), ?_, ?_⟩
  · have h : ∀ i j : Fin n, ¬ (s = i ∧ t = j) → Matrix.transvection s t c i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
      intro i j hij
      simp [Matrix.transvection, Matrix.single, hij]
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij hz' => ?_⟩
    · have hij : j < i := hij
      show Matrix.transvection s t c i j = 0
      rw [h i j (by omega), Matrix.one_apply_ne (by omega)]
    · show Matrix.transvection s t c i i = 1
      rw [h i i (by omega), Matrix.one_apply_eq]
    · show Matrix.transvection s t c i j = 0
      rw [h i j (by rintro ⟨rfl, rfl⟩; exact hz hz'), Matrix.one_apply_ne (by omega)]
  · show Matrix.transvection s t c s t = c
    simp [Matrix.transvection, hne]

omit [Fintype F] in
theorem exists_perm (σ : Equiv.Perm (Fin n)) : ∃ g : GL (Fin n) F,
    (∀ a j, (g : Matrix (Fin n) (Fin n) F) a j = if a = σ j then 1 else 0) ∧
    ∀ (s : GL (Fin n) F) i j, ((g⁻¹ * s * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (s : Matrix (Fin n) (Fin n) F) (σ i) (σ j) := by
  refine ⟨⟨Matrix.of fun a j => if a = σ j then 1 else 0, Matrix.of fun i a => if a = σ i then 1 else 0, ?_, ?_⟩,
    fun _ _ => rfl, fun s i j => ?_⟩
  · ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
    · simp [Matrix.one_apply, eq_comm]
    · intro l _ hl
      have : a ≠ σ l := fun h => hl (by simp [h])
      simp [this]
    · simp
  · ext a b
    simp [Matrix.mul_apply, Matrix.one_apply, eq_comm]
  · simp [Matrix.mul_apply]

omit [Fintype F] in
theorem exists_diag (d : Fin n → F) (hd : ∀ i, d i ≠ 0) : ∃ g : GL (Fin n) F,
    (g : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d ∧
    ∀ (s : GL (Fin n) F) i j, ((g⁻¹ * s * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (d i)⁻¹ * (s : Matrix (Fin n) (Fin n) F) i j * d j := by
  refine ⟨⟨Matrix.diagonal d, Matrix.diagonal fun i => (d i)⁻¹, ?_, ?_⟩, rfl, fun s i j => ?_⟩
  · simp [hd]
  · simp [hd]
  · simp

end Concrete

section Main

variable {F : Type} [Field F] [Fintype F] {n : ℕ} {P : Subgroup (GL (Fin n) F)} {V : Type} [AddCommGroup V] [Module ℂ V]

def dm (π : Representation ℂ P V) (ψ : AddChar F ℂ) (H : Subgroup (GL (Fin n) F)) (f : GL (Fin n) F → F) : ℕ :=
  finrank ℂ (eig π (H.subgroupOf P : Set P) fun p => ψ (f p))

variable (π : Representation ℂ P V) {ψ : AddChar F ℂ}

omit [Fintype F] in
theorem dm_congr {H H' : Subgroup (GL (Fin n) F)} {f f' : GL (Fin n) F → F} (h : ∀ u, u ∈ H ↔ u ∈ H')
    (hf : ∀ u ∈ H, f u = f' u) : dm π ψ H f = dm π ψ H' f' := by
  unfold dm
  rw [eig_congr π (S := (H.subgroupOf P : Set P)) (S' := (H'.subgroupOf P : Set P)) (χ := fun p => ψ (f p)) (χ' := fun p => ψ (f' p)) (fun g => h g)
    (fun g hg => by rw [hf g hg])]

variable [FiniteDimensional ℂ V]

omit [Fintype F] in
theorem dm_conj_le {H H' : Subgroup (GL (Fin n) F)} {f f' : GL (Fin n) F → F} {g : GL (Fin n) F} (hg : g ∈ P)
    (h : ∀ s ∈ H', g⁻¹ * s * g ∈ H ∧ f (g⁻¹ * s * g) = f' s) : dm π ψ H f ≤ dm π ψ H' f' :=
  finrank_eig_conj_le π (⟨g, hg⟩ : P) fun s hs => ⟨(h s hs).1, congrArg ψ (h s hs).2⟩

theorem dm_step (hψ : ψ ≠ 1) (hU : unip F n ≤ P) (Ed : Fin n → Fin n → Prop) [DecidableRel Ed]
    (hE : ∀ i j, Ed i j → j.val = i.val + 1) {a e m : Fin n} (hae : a < e) (hem : e < m) :
    dm π ψ (pat F n a e e m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) =
      dm π ψ (pat F n a (e + 1) (e + 1) m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) := by
  refine finrank_eig_exchange π hψ ((pat F n a e (e + 1) m).subgroupOf P) _ _
    (fun p => edgeSum Ed (p : GL (Fin n) F) + ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a m)
    (fun p => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a e)
    (fun p => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) e m) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx y hy
    rw [Subgroup.mem_subgroupOf, mem_pat] at hx hy
    rw [Subgroup.coe_mul, edgeSum_mul Ed hE hx.1 hy.1, unip_mul_entry_exc hx.1 hy.1 hae hem]
    · ring
    · intro l h1 h2 h3
      rcases lt_or_gt_of_ne h3 with h | h
      · rw [hx.2 a l h1 (Or.inl ⟨rfl, h⟩), zero_mul]
      · rw [hy.2 l m h2 (Or.inr ⟨by omega, rfl⟩), mul_zero]
  · intro x hx y hy
    rw [Subgroup.mem_subgroupOf, mem_pat] at hx hy
    exact unip_mul_entry hx.1 hy.1 hae fun l h1 h2 => by rw [hx.2 a l h1 (Or.inl ⟨rfl, h2⟩), zero_mul]
  · intro x hx y hy
    rw [Subgroup.mem_subgroupOf, mem_pat] at hx hy
    exact unip_mul_entry hx.1 hy.1 hem fun l h1 h2 => by rw [hy.2 l m h2 (Or.inr ⟨by omega, rfl⟩), mul_zero]
  · intro x
    simp only [Subgroup.mem_subgroupOf, mem_pat]
    constructor
    · exact fun h => ⟨⟨h.1, fun i j hij hz => h.2 i j hij (by omega)⟩, h.2 e m hem (by omega)⟩
    · refine fun h => ⟨h.1.1, fun i j hij hz => ?_⟩
      by_cases h' : i = e ∧ j = m
      · rw [h'.1, h'.2]; exact h.2
      · exact h.1.2 i j hij (by omega)
  · intro x
    simp only [Subgroup.mem_subgroupOf, mem_pat]
    constructor
    · exact fun h => ⟨⟨h.1, fun i j hij hz => h.2 i j hij (by omega)⟩, h.2 a e hae (by omega)⟩
    · refine fun h => ⟨h.1.1, fun i j hij hz => ?_⟩
      by_cases h' : i = a ∧ j = e
      · rw [h'.1, h'.2]; exact h.2
      · exact h.1.2 i j hij (by omega)
  · intro t
    obtain ⟨u, hu, h⟩ := exists_transv (F := F) (a := a) (e := e) (e' := e) (m := m) hae (by omega) t
    exact ⟨⟨u, hU hu.1⟩, hu, h⟩
  · intro t
    obtain ⟨u, hu, h⟩ := exists_transv (F := F) (a := a) (e := e + 1) (e' := e + 1) (m := m) hem (by omega) t
    exact ⟨⟨u, hU hu.1⟩, hu, h⟩

theorem dm_chain (hψ : ψ ≠ 1) (hU : unip F n ≤ P) (Ed : Fin n → Fin n → Prop) [DecidableRel Ed]
    (hE : ∀ i j, Ed i j → j.val = i.val + 1) {a m : Fin n} (ham : a < m) :
    dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) =
      dm π ψ (pat F n a m m m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) := by
  have key : ∀ e : ℕ, a.val + 1 ≤ e → e ≤ m.val →
      dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) =
      dm π ψ (pat F n a e e m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) := by
    intro e he
    induction e, he using Nat.le_induction with
    | base =>
      intro _
      refine dm_congr π (fun u => ?_) fun _ _ => rfl
      simp only [mem_pat]
      exact and_congr_right fun _ => ⟨fun h i j hij hz => h i j hij (by omega), fun h i j hij hz => h i j hij (by omega)⟩
    | succ e he ih =>
      intro h
      rw [ih (by omega)]
      exact dm_step π hψ hU Ed hE (e := ⟨e, by omega⟩) (by show a.val < e; omega) (by show e < m.val; omega)
  exact key m (by omega) le_rfl

theorem dm_sym_succ (hψ : ψ ≠ 1) (hU : unip F n ≤ P) {a m : Fin n} {c : ℕ} (h : m.val = a.val + 1 + c) :
    dm π ψ (pat F n 0 0 (a + 1) m) (edgeSum (symEdge (a.val + 1) c)) =
      dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + (u : Matrix (Fin n) (Fin n) F) a m) := by
  let Ed : Fin n → Fin n → Prop := fun i j => j.val = i.val + 1 ∧ i.val ≠ a.val ∧ i.val + 1 ≠ m.val
  have e1 : dm π ψ (pat F n 0 0 (a + 1) m) (edgeSum (symEdge (a.val + 1) c)) =
      dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum Ed u + (u : Matrix (Fin n) (Fin n) F) a m) :=
    dm_congr π (fun _ => Iff.rfl) fun u _ => (edgeSum_add Ed _ a m (by simp [Ed])
      (fun i j => by simp only [symEdge, Ed]; omega) u).symm
  rw [e1, dm_chain π hψ hU Ed (fun i j h => h.1) (by omega),
    dm_chain π hψ hU (cutEdge m) (fun i j h => h.1) (by omega)]
  refine dm_congr π (fun _ => Iff.rfl) fun u hu => ?_
  congr 1
  refine edgeSum_congr _ _ 1 fun i j => ?_
  simp only [Equiv.Perm.coe_one, id, cutEdge, Ed, and_true, and_self]
  by_cases hz : i < j ∧ i = a ∧ j < m
  · exact Or.inr (Or.inr (hu.2 i j hz.1 (by omega)))
  · by_cases h1 : j.val = i.val + 1 ∧ i.val + 1 ≠ m.val
    · left; omega
    · right; left; omega

def cyc (a b : Fin n) (h : a ≤ b) : Equiv.Perm (Fin n) where
  toFun i := ⟨if a.val ≤ i.val ∧ i.val < b.val then i.val + 1 else if i.val = b.val then a.val else i.val,
    by split_ifs <;> omega⟩
  invFun i := ⟨if a.val < i.val ∧ i.val ≤ b.val then i.val - 1 else if i.val = a.val then b.val else i.val,
    by split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp only
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    dsimp only
    split_ifs <;> omega

theorem cyc_val (a b : Fin n) (h : a ≤ b) (i : Fin n) :
    (a.val ≤ i.val ∧ i.val < b.val ∧ (cyc a b h i).val = i.val + 1) ∨ (i.val = b.val ∧ (cyc a b h i).val = a.val) ∨
      ((i.val < a.val ∨ b.val < i.val) ∧ (cyc a b h i).val = i.val) := by
  simp only [cyc, Equiv.coe_fn_mk]
  split_ifs <;> omega

theorem dm_perm_le (σ : Equiv.Perm (Fin n))
    (hσ : ∀ g : GL (Fin n) F, (∀ a j, (g : Matrix (Fin n) (Fin n) F) a j = if a = σ j then 1 else 0) → g ∈ P)
    (Ed Ed' : Fin n → Fin n → Prop) [DecidableRel Ed] [DecidableRel Ed'] {a e e' m a₁ e₁ e₁' m₁ : ℕ}
    (h1 : ∀ i j : Fin n, j < i ∨ (i < j ∧ ((i.val = a ∧ j.val < e) ∨ (e' ≤ i.val ∧ j.val = m))) →
      σ j < σ i ∨ (σ i < σ j ∧ (((σ i).val = a₁ ∧ (σ j).val < e₁) ∨ (e₁' ≤ (σ i).val ∧ (σ j).val = m₁))))
    (h2 : ∀ i j : Fin n, (Ed i j ∧ Ed' (σ i) (σ j)) ∨ (¬ Ed i j ∧ ¬ Ed' (σ i) (σ j)) ∨
      σ j < σ i ∨ (σ i < σ j ∧ (((σ i).val = a₁ ∧ (σ j).val < e₁) ∨ (e₁' ≤ (σ i).val ∧ (σ j).val = m₁)))) :
    dm π ψ (pat F n a e e' m) (edgeSum Ed) ≤ dm π ψ (pat F n a₁ e₁ e₁' m₁) (edgeSum Ed') := by
  obtain ⟨g, hg, hc⟩ := exists_perm (F := F) σ
  refine dm_conj_le π (hσ g hg) fun s hs => ?_
  have hz : ∀ i j : Fin n, j < i ∨ (i < j ∧ ((i.val = a₁ ∧ j.val < e₁) ∨ (e₁' ≤ i.val ∧ j.val = m₁))) →
      (s : Matrix (Fin n) (Fin n) F) i j = 0 := by
    rintro i j (h | h)
    · exact unip_lower hs.1 h
    · exact hs.2 i j h.1 h.2
  refine ⟨⟨mem_unip.2 ⟨fun i j h => ?_, fun i => ?_⟩, fun i j h h' => ?_⟩, edgeSum_congr _ _ σ fun i j => ?_⟩
  · rw [hc]; exact hz _ _ (h1 i j (Or.inl h))
  · rw [hc]; exact unip_diag hs.1 _
  · rw [hc]; exact hz _ _ (h1 i j (Or.inr ⟨h, h'⟩))
  · rw [hc]
    rcases h2 i j with h | h | h
    · exact Or.inl ⟨h.1, h.2, rfl⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hz _ _ h, hz _ _ h⟩)

set_option maxHeartbeats 1000000 in
theorem dm_perm (hψ : ψ ≠ 1) (hU : unip F n ≤ P) {a m : Fin n} {c : ℕ} (h : m.val = a.val + 1 + c)
    (hσ : ∀ σ : Equiv.Perm (Fin n), (∀ i, m ≤ i → σ i = i) →
      ∀ g : GL (Fin n) F, (∀ a j, (g : Matrix (Fin n) (Fin n) F) a j = if a = σ j then 1 else 0) → g ∈ P) :
    dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + (u : Matrix (Fin n) (Fin n) F) a m) =
      dm π ψ (pat F n 0 0 a (a + c)) (edgeSum (symEdge a c)) := by
  let Ed : Fin n → Fin n → Prop := fun i j => (j.val = i.val + 1 ∧ i.val + 1 ≠ m.val) ∨ (i.val = a.val ∧ j.val = m.val)
  have e1 : dm π ψ (pat F n a m m m) (fun u => edgeSum (cutEdge m) u + (u : Matrix (Fin n) (Fin n) F) a m) =
      dm π ψ (pat F n a m m m) (edgeSum Ed) :=
    dm_congr π (fun _ => Iff.rfl) fun u _ => edgeSum_add _ Ed a m (by simp only [cutEdge]; omega)
      (fun i j => by simp only [cutEdge, Ed]; omega) u
  rw [dm_chain π hψ hU (cutEdge m) (fun i j h => h.1) (by omega), e1]
  let b : Fin n := ⟨a + c, by omega⟩
  have hb : b.val = a + c := rfl
  have hab : a ≤ b := by show a.val ≤ a + c; omega
  have hfix : ∀ i, m ≤ i → cyc a b hab i = i := fun i hi => by
    have := cyc_val a b hab i
    omega
  have hinv : ∀ i : Fin n, _ := fun i => by
    have := cyc_val a b hab ((cyc a b hab).symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this
  apply le_antisymm
  · refine dm_perm_le π (cyc a b hab).symm (hσ _ fun i hi => ?_) _ _ (fun i j => ?_) (fun i j => ?_)
    · rw [Equiv.symm_apply_eq, hfix i hi]
    · have := hinv i
      have := hinv j
      omega
    · have := hinv i
      have := hinv j
      simp only [Ed, symEdge]
      omega
  · refine dm_perm_le π (cyc a b hab) (hσ _ hfix) _ _ (fun i j => ?_) (fun i j => ?_)
    · have := cyc_val a b hab i
      have := cyc_val a b hab j
      omega
    · simp only [Ed, symEdge]
      rcases cyc_val a b hab i with h1 | h1 | h1 <;> rcases cyc_val a b hab j with h2 | h2 | h2 <;> omega

theorem dm_torus_le {a m : Fin n} (ham : a < m)
    (hD : ∀ (d : Fin n → F) (g : GL (Fin n) F), (∀ i, m ≤ i → d i = 1) →
      (g : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d → g ∈ P) {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + s * (u : Matrix (Fin n) (Fin n) F) a m) ≤
      dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + t * (u : Matrix (Fin n) (Fin n) F) a m) := by
  have hd : ∀ i : Fin n, (if i < m then s / t else 1) ≠ 0 := fun i => by
    split_ifs
    · exact div_ne_zero hs ht
    · exact one_ne_zero
  obtain ⟨g, hg, hc⟩ := exists_diag (fun i : Fin n => if i < m then s / t else 1) hd
  refine dm_conj_le π (hD _ g (fun i hi => if_neg (not_lt.2 hi)) hg) fun u hu => ?_
  refine ⟨⟨mem_unip.2 ⟨fun i j h => ?_, fun i => ?_⟩, fun i j h h' => ?_⟩, ?_⟩
  · rw [hc, unip_lower hu.1 h, mul_zero, zero_mul]
  · rw [hc, unip_diag hu.1, mul_one, inv_mul_cancel₀ (hd i)]
  · rw [hc, hu.2 i j h h', mul_zero, zero_mul]
  · rw [hc, if_pos ham, if_neg (lt_irrefl m)]
    congr 1
    · refine edgeSum_congr _ _ 1 fun i j => ?_
      simp only [Equiv.Perm.coe_one, id]
      by_cases h : cutEdge m i j
      · refine Or.inl ⟨h, h, ?_⟩
        have h' : (if j < m then s / t else 1) = (if i < m then s / t else 1) :=
          if_congr (by unfold cutEdge at h; omega) rfl rfl
        rw [hc, h', mul_right_comm, inv_mul_cancel₀ (hd i), one_mul]
      · exact Or.inr (Or.inl ⟨h, h⟩)
    · field_simp

theorem dm_fourier (hψ : ψ ≠ 1) (hU : unip F n ≤ P) {a m : Fin n} (ham : a < m)
    (hD : ∀ (d : Fin n → F) (g : GL (Fin n) F), (∀ i, m ≤ i → d i = 1) →
      (g : Matrix (Fin n) (Fin n) F) = Matrix.diagonal d → g ∈ P) :
    dm π ψ (pat F n 0 0 a m) (edgeSum (cutEdge m)) = dm π ψ (pat F n 0 0 (a + 1) m) (edgeSum (cutEdge m)) +
      (Fintype.card F - 1) *
        dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + (u : Matrix (Fin n) (Fin n) F) a m) := by
  classical
  have h1 : dm π ψ (pat F n 0 0 a m) (edgeSum (cutEdge m)) = ∑ c : F,
      dm π ψ (pat F n 0 0 (a + 1) m) (fun u => edgeSum (cutEdge m) u + c * (u : Matrix (Fin n) (Fin n) F) a m) := by
    refine finrank_eig_fourier π hψ ((pat F n 0 0 (a + 1) m).subgroupOf P) _
      (fun p => edgeSum (cutEdge m) (p : GL (Fin n) F))
      (fun p => ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a m) ?_ ?_ ?_ ?_
    · intro x hx y hy
      exact edgeSum_mul _ (fun i j h => h.1) hx.1 hy.1
    · intro x hx y hy
      rw [Subgroup.mem_subgroupOf, mem_pat] at hx hy
      exact unip_mul_entry hx.1 hy.1 ham fun l h1 h2 => by rw [hy.2 l m h2 (Or.inr ⟨by omega, rfl⟩), mul_zero]
    · intro t
      obtain ⟨u, hu, h⟩ := exists_transv (F := F) (a := 0) (e := 0) (e' := a + 1) (m := m) ham (by omega) t
      exact ⟨⟨u, hU hu.1⟩, hu, h⟩
    · intro x
      simp only [Subgroup.mem_subgroupOf, mem_pat]
      constructor
      · exact fun h => ⟨⟨h.1, fun i j hij hz => h.2 i j hij (by omega)⟩, h.2 a m ham (by omega)⟩
      · refine fun h => ⟨h.1.1, fun i j hij hz => ?_⟩
        by_cases h' : i = a ∧ j = m
        · rw [h'.1, h'.2]; exact h.2
        · exact h.1.2 i j hij (by omega)
  rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F)),
    Finset.sum_congr rfl fun c hc => le_antisymm
      (dm_torus_le π ham hD (Finset.ne_of_mem_erase hc) one_ne_zero)
      (dm_torus_le π ham hD one_ne_zero (Finset.ne_of_mem_erase hc)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
  simp only [zero_mul, add_zero, one_mul]

end Main

theorem mirabolic_whittaker (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (k : ℕ)
    (P : Subgroup (GL (Fin (k + 1)) F))
    (hP : ∀ g, g ∈ P ↔ ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Representation ℂ P V) :
    finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k}
        fun p => ψ (edgeSum (symEdge 0 k) (p : GL (Fin (k + 1)) F))) =
      ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) *
        finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unip F (k + 1)}
          fun p => ψ (edgeSum (cutEdge (j)) (p : GL (Fin (k + 1)) F))) := by
  have hU : unip F (k + 1) ≤ P := fun g hg => (hP g).2 fun j => by
    rcases (Fin.le_last j).eq_or_lt with h | h
    · rw [h, unip_diag hg, Matrix.one_apply_eq]
    · rw [unip_lower hg h, Matrix.one_apply_ne h.ne']
  have hσ : ∀ m : Fin (k + 1), ∀ σ : Equiv.Perm (Fin (k + 1)), (∀ i, m ≤ i → σ i = i) →
      ∀ g : GL (Fin (k + 1)) F,
        (∀ a j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) a j = if a = σ j then 1 else 0) → g ∈ P := by
    intro m σ h g hg
    refine (hP g).2 fun j => ?_
    rw [hg, Matrix.one_apply]
    refine if_congr ?_ rfl rfl
    conv_lhs => rw [← h _ (Fin.le_last m)]
    exact σ.apply_eq_iff_eq
  have hD : ∀ m : Fin (k + 1), ∀ (d : Fin (k + 1) → F) (g : GL (Fin (k + 1)) F), (∀ i, m ≤ i → d i = 1) →
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = Matrix.diagonal d → g ∈ P := by
    intro m d g h hg
    refine (hP g).2 fun j => ?_
    rw [hg, Matrix.diagonal_apply, h _ (Fin.le_last m), Matrix.one_apply]
  let S : ℕ → ℕ → ℕ := fun a c => dm π ψ (pat F (k + 1) 0 0 a (a + c)) (edgeSum (symEdge a c))
  let T : ℕ → ℕ → ℕ := fun a m => dm π ψ (pat F (k + 1) 0 0 a m) (edgeSum (cutEdge m))
  let D : ℕ → ℕ := fun m => dm π ψ (unip F (k + 1)) (edgeSum (cutEdge m))
  have hS : ∀ c a, a + c ≤ k → S a c = T 0 c := by
    intro c a
    induction a with
    | zero =>
      intro _
      refine dm_congr π (fun u => by rw [zero_add]) fun u _ => edgeSum_congr _ _ 1 fun i j => ?_
      simp only [Equiv.Perm.coe_one, id, cutEdge, symEdge, and_true, and_self]
      by_cases h1 : j.val = i.val + 1 ∧ i.val + 1 ≠ c
      · left; omega
      · right; left; omega
    | succ a ih =>
      intro h
      rw [← ih (by omega)]
      exact (dm_sym_succ π hψ hU (a := ⟨a, by omega⟩) (m := ⟨a + 1 + c, by omega⟩) rfl).trans
        (dm_perm π hψ hU rfl (hσ _))
  have hT : ∀ m ≤ k, ∀ c a, a + c = m →
      T a m = D m + (Fintype.card F - 1) * ∑ l ∈ Finset.range c, T 0 l := by
    intro m hm c
    induction c with
    | zero =>
      intro a ha
      rw [Finset.sum_range_zero, mul_zero, add_zero]
      exact dm_congr π (fun u => ⟨fun h => h.1, fun h => ⟨h, fun i j h1 h2 => by omega⟩⟩) fun _ _ => rfl
    | succ c ih =>
      intro a ha
      have h1 := dm_fourier π hψ hU (a := ⟨a, by omega⟩) (m := ⟨m, by omega⟩) (by show a < m; omega) (hD _)
      rw [dm_perm π hψ hU (c := c) (by show m = a + 1 + c; omega) (hσ _)] at h1
      have h2 : T a m = T (a + 1) m + (Fintype.card F - 1) * S a c := h1
      rw [h2, ih (a + 1) (by omega), hS c a (by omega), Finset.sum_range_succ]
      ring
  have h := solve_rec (Fintype.card F) Fintype.card_pos k (T 0) D (fun m hm => hT m hm m 0 (zero_add m)) k le_rfl
  rw [← hS k 0 (by omega)] at h
  refine Eq.trans ?_ h
  refine dm_congr π (H := unipSym F (k + 1) 0 k) (f := edgeSum (symEdge 0 k)) (fun u => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.1, fun i j h1 h2 => h.2 i j (by omega) (by omega) (by omega)⟩,
    fun h => ⟨h.1, fun i j h1 h2 h3 => h.2 i j (by omega) (by omega)⟩⟩

end GlobalTheory.FinGL.Mir
