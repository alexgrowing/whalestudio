import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Set

section Cosets

variable {α : Type*} [Group α] {W : Type*} [AddCommGroup W]

theorem sum_quotient_out_of_le {s t : Subgroup α} (h : s ≤ t) [Fintype (α ⧸ s)] [Fintype (α ⧸ t)]
    [Fintype (t ⧸ s.subgroupOf t)] (φ : α → W) (hφ : ∀ a, ∀ b ∈ t, φ (a * b) = φ a) :
    ∑ q : α ⧸ s, φ (Quotient.out q) = (s.relIndex t) • ∑ q : α ⧸ t, φ (Quotient.out q) := by
  classical
  set e := Subgroup.quotientEquivProdOfLE h
  have key : ∀ a : α ⧸ s, φ (Quotient.out a) = φ (Quotient.out (e a).1) := by
    intro a
    have h1 : (e a).1 = (QuotientGroup.mk (Quotient.out a) : α ⧸ t) := by
      conv_lhs => rw [← Quotient.out_eq' a]
      rfl
    rw [h1]
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul t (Quotient.out a)
    rw [hb, hφ _ _ b.2]
  rw [Fintype.sum_congr _ _ key, e.sum_comp (fun p => φ (Quotient.out p.1)), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Finset.smul_sum, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end Cosets

section Average

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

def rightStab (f : G → W) : Subgroup G where
  carrier := {g | ∀ x, f (x * g) = f x}
  mul_mem' {a b} ha hb x := by
    show f (x * (a * b)) = f x
    rw [← mul_assoc, hb, ha]
  one_mem' x := by
    show f (x * 1) = f x
    rw [mul_one]
  inv_mem' {a} ha x := by
    show f (x * a⁻¹) = f x
    have := ha (x * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

omit [AddCommGroup W] [Module ℂ W] in
theorem mem_rightStab {f : G → W} {g : G} : g ∈ rightStab f ↔ ∀ x, f (x * g) = f x :=
  Iff.rfl

def avgSub (K : Subgroup G) (S : Subgroup K) (f : G → W) (x : G) : W :=
  ((S.index : ℂ)⁻¹) • ∑ᶠ q : K ⧸ S, f (x * ((Quotient.out q : K) : G))

def avgOver (K : Subgroup G) (f : G → W) (x : G) : W :=
  avgSub K ((rightStab f).subgroupOf K) f x

theorem avgSub_eq_sum (K : Subgroup G) (S : Subgroup K) [Fintype (K ⧸ S)] (f : G → W) (x : G) :
    avgSub K S f x = ((S.index : ℂ)⁻¹) • ∑ q : K ⧸ S, f (x * ((Quotient.out q : K) : G)) := by
  rw [avgSub, finsum_eq_sum_of_fintype]

variable {K : Subgroup G} {f : G → W}

theorem avgOver_eq_avgSub {S : Subgroup K} (hS : S ≤ (rightStab f).subgroupOf K) (hSi : S.index ≠ 0)
    (x : G) : avgOver K f x = avgSub K S f x := by
  classical
  set t := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hSi⟩
  have hti : t.index ≠ 0 := fun h0 => hSi (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hS))
  have : t.FiniteIndex := ⟨hti⟩
  have hrel : S.relIndex t ≠ 0 := by
    intro h0
    apply hSi
    rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
  have : (S.subgroupOf t).FiniteIndex := ⟨hrel⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  let _ := Fintype.ofFinite (K ⧸ t)
  let _ := Fintype.ofFinite (t ⧸ S.subgroupOf t)
  rw [avgOver, avgSub_eq_sum, avgSub_eq_sum,
    sum_quotient_out_of_le hS (fun k : K => f (x * (k : G))) (fun a b hb => by
      show f (x * ((a : G) * (b : G))) = f (x * a)
      rw [← mul_assoc]
      exact hb _),
    ← Subgroup.relIndex_mul_index hS, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_mul]
  congr 1
  have : (S.relIndex t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hrel
  have h2 : (t.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hti
  field_simp
  exact div_self h2

abbrev AvgFinite (K : Subgroup G) (f : G → W) : Prop := (rightStab f).relIndex K ≠ 0

theorem avgOver_eq_sum [Fintype (K ⧸ (rightStab f).subgroupOf K)] (x : G) :
    avgOver K f x = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, f (x * ((Quotient.out q : K) : G)) := by
  rw [avgOver, avgSub_eq_sum]
  rfl

theorem avgOver_mul_right (hf : AvgFinite K f) {k : G} (hk : k ∈ K) (x : G) :
    avgOver K f (x * k) = avgOver K f x := by
  classical
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  simp only [avgOver]
  rw [avgSub_eq_sum, avgSub_eq_sum]
  congr 1
  let k' : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (MulAction.toPerm k') _ _ fun q => ?_
  show f (x * k * (Quotient.out q : K)) = f (x * (Quotient.out (k' • q) : K))
  have h1 : k' • q = (QuotientGroup.mk (k' * Quotient.out q) : K ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h1]
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul S (k' * Quotient.out q)
  rw [hb]
  have hb' : ((b : K) : G) ∈ rightStab f := b.2
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, ← mul_assoc, hb' _, mul_assoc]

theorem le_rightStab_avgOver (hf : AvgFinite K f) : K ≤ rightStab (avgOver K f) :=
  fun _ hk x => avgOver_mul_right hf hk x

theorem avgOver_comp_linearMap (hf : AvgFinite K f) {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') (x : G) :
    avgOver K (fun y => T (f y)) x = T (avgOver K f x) := by
  classical
  have hle : (rightStab f).subgroupOf K ≤ (rightStab fun y => T (f y)).subgroupOf K :=
    fun k hk y => by
      show T (f (y * (k : G))) = T (f y)
      exact congrArg T (hk y)
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_avgSub hle hf, avgOver, avgSub_eq_sum, avgSub_eq_sum, map_smul, map_sum]

theorem avgOver_comp_mul_left (h x : G) :
    avgOver K (fun y => f (h * y)) x = avgOver K f (h * x) := by
  have hst : rightStab (fun y => f (h * y)) = rightStab f := by
    ext g
    simp only [mem_rightStab]
    constructor
    · intro H y
      have := H (h⁻¹ * y)
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this
    · intro H y
      rw [← mul_assoc, H]
  rw [avgOver, avgOver, avgSub, avgSub, hst]
  simp only [mul_assoc]

end Average

section Average2

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}

theorem avgSub_comp_mul_right_of_normal {S : Subgroup K} [S.Normal] (hSi : S.index ≠ 0)
    (hS : S ≤ (rightStab f).subgroupOf K) {k : G} (hk : k ∈ K) (x : G) :
    avgSub K S (fun y => f (y * k)) x = avgSub K S f x := by
  classical
  have : S.FiniteIndex := ⟨hSi⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  rw [avgSub_eq_sum, avgSub_eq_sum]
  congr 1
  let k' : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk k' : K ⧸ S)) _ _ fun q => ?_
  show f (x * ((Quotient.out q : K) : G) * k) =
    f (x * ((Quotient.out (q * (QuotientGroup.mk k' : K ⧸ S)) : K) : G))
  have h1 : q * (QuotientGroup.mk k' : K ⧸ S) = QuotientGroup.mk (Quotient.out q * k') := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [h1]
  obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul S (Quotient.out q * k')
  rw [hb]
  have hb' : ((b : K) : G) ∈ rightStab f := hS b.2
  simp only [Subgroup.coe_mul]
  rw [← mul_assoc, ← mul_assoc, hb' _, mul_assoc]

theorem avgOver_comp_mul_right (hf : AvgFinite K f) {k : G} (hk : k ∈ K) :
    avgOver K (fun y => f (y * k)) = avgOver K f := by
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  set N := S.normalCore
  have hNi : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hN1 : N ≤ S := Subgroup.normalCore_le S
  have hN2 : N ≤ (rightStab fun y => f (y * k)).subgroupOf K := by
    intro n hn y
    show f (y * (n : G) * k) = f (y * k)
    let k' : K := ⟨k, hk⟩
    have hc : k'⁻¹ * n * k' ∈ N := by
      have := (Subgroup.normalCore_normal S).conj_mem n hn k'⁻¹
      simpa using this
    have hc' : ((k'⁻¹ * n * k' : K) : G) ∈ rightStab f := hN1 hc
    have := hc' (y * k)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    congr 1
    simp only [k']
    group
  funext x
  rw [avgOver_eq_avgSub hN2 hNi, avgOver_eq_avgSub hN1 hNi]
  exact avgSub_comp_mul_right_of_normal hNi hN1 hk x

theorem avgOver_of_forall (h : ∀ k ∈ K, ∀ y, f (y * k) = f y) : avgOver K f = f := by
  classical
  have hle : (⊤ : Subgroup K) ≤ (rightStab f).subgroupOf K := fun k _ => h k k.2
  have hi : (⊤ : Subgroup K).index ≠ 0 := by rw [Subgroup.index_top]; exact one_ne_zero
  have : (⊤ : Subgroup K).FiniteIndex := ⟨hi⟩
  let _ := Fintype.ofFinite (K ⧸ (⊤ : Subgroup K))
  funext x
  rw [avgOver_eq_avgSub hle hi, avgSub_eq_sum]
  have hterm : ∀ q : K ⧸ (⊤ : Subgroup K), f (x * ((Quotient.out q : K) : G)) = f x :=
    fun q => h _ (Quotient.out q).2 x
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Subgroup.index, Subgroup.index_top, one_smul, Nat.cast_one,
    inv_one, one_smul]

theorem avgOver_add {g : G → W} (hf : AvgFinite K f) (hg : AvgFinite K g) :
    avgOver K (f + g) = avgOver K f + avgOver K g := by
  classical
  set S := (rightStab f ⊓ rightStab g).subgroupOf K
  have hSi : S.index ≠ 0 := Subgroup.relIndex_inf_ne_zero hf hg
  have h1 : S ≤ (rightStab f).subgroupOf K := fun k hk => (Subgroup.mem_inf.1 hk).1
  have h2 : S ≤ (rightStab g).subgroupOf K := fun k hk => (Subgroup.mem_inf.1 hk).2
  have h3 : S ≤ (rightStab (f + g)).subgroupOf K := fun k hk y => by
    show f (y * (k : G)) + g (y * (k : G)) = f y + g y
    exact congrArg₂ (· + ·) ((Subgroup.mem_inf.1 hk).1 y) ((Subgroup.mem_inf.1 hk).2 y)
  have : S.FiniteIndex := ⟨hSi⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  funext x
  rw [Pi.add_apply, avgOver_eq_avgSub h3 hSi, avgOver_eq_avgSub h1 hSi, avgOver_eq_avgSub h2 hSi,
    avgSub_eq_sum, avgSub_eq_sum, avgSub_eq_sum, ← smul_add, ← Finset.sum_add_distrib]
  rfl

theorem avgOver_smul (c : ℂ) (hf : AvgFinite K f) : avgOver K (c • f) = c • avgOver K f := by
  funext x
  have := avgOver_comp_linearMap hf (c • LinearMap.id) x
  show avgOver K (fun y => c • f y) x = c • avgOver K f x
  simpa using this

theorem avgOver_eq_sum_translates
    [Fintype (K ⧸ (rightStab f).subgroupOf K)] :
    avgOver K f = (((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K, fun y => f (y * ((Quotient.out q : K) : G)) := by
  funext x
  rw [avgOver_eq_sum, Pi.smul_apply, Finset.sum_apply]

theorem avgOver_mem (hf : AvgFinite K f) {V : Submodule ℂ (G → W)}
    (hV : ∀ k ∈ K, (fun y => f (y * k)) ∈ V) : avgOver K f ∈ V := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  rw [avgOver_eq_sum_translates]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hV _ (Quotient.out q).2)

theorem sub_avgOver_mem_span (hf : AvgFinite K f) :
    f - avgOver K f ∈ Submodule.span ℂ {g | ∃ k ∈ K, g = (fun y => f (y * k)) - f} := by
  classical
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  have hI : (((rightStab f).relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hf
  have hcard : Fintype.card (K ⧸ (rightStab f).subgroupOf K) = (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have key : f - avgOver K f = -((((rightStab f).relIndex K : ℂ)⁻¹) •
      ∑ q : K ⧸ (rightStab f).subgroupOf K,
        ((fun y => f (y * ((Quotient.out q : K) : G))) - f)) := by
    rw [avgOver_eq_sum_translates, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul, inv_mul_cancel₀ hI, one_smul,
      neg_sub]
  rw [key]
  refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))
  exact Submodule.subset_span ⟨_, (Quotient.out q).2, rfl⟩

theorem relIndex_ne_zero_of_le_right {H K K' : Subgroup G} (hKK' : K ≤ K')
    (h : H.relIndex K' ≠ 0) : H.relIndex K ≠ 0 := by
  have : (H.subgroupOf K').FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKK').injective
  exact Subgroup.index_ne_zero_of_finite

theorem avgOver_avgOver {K' : Subgroup G} (hKK' : K ≤ K') (hf' : AvgFinite K' f) :
    avgOver K' (avgOver K f) = avgOver K' f := by
  classical
  have hf : AvgFinite K f := relIndex_ne_zero_of_le_right hKK' hf'
  set S' := (rightStab f).subgroupOf K'
  have : S'.FiniteIndex := ⟨hf'⟩
  set N := S'.normalCore
  have hNi : N.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hN1 : N ≤ S' := Subgroup.normalCore_le S'
  have : ((rightStab f).subgroupOf K).FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ (rightStab f).subgroupOf K)
  have : N.FiniteIndex := ⟨hNi⟩
  let _ := Fintype.ofFinite (K' ⧸ N)

  have hN2 : N ≤ (rightStab (avgOver K f)).subgroupOf K' := by
    intro n hn y
    show avgOver K f (y * (n : G)) = avgOver K f y
    rw [avgOver_eq_sum, avgOver_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    set k : K := Quotient.out q
    let k' : K' := ⟨k, hKK' k.2⟩
    have hc : k'⁻¹ * n * k' ∈ N := by
      have := (Subgroup.normalCore_normal S').conj_mem n hn k'⁻¹
      simpa using this
    have hc' : ((k'⁻¹ * n * k' : K') : G) ∈ rightStab f := hN1 hc
    have := hc' (y * (k : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, k'] at this
    rw [← this]
    congr 1
    group
  funext x
  rw [avgOver_eq_avgSub hN2 hNi, avgOver_eq_avgSub hN1 hNi, avgSub_eq_sum, avgSub_eq_sum]
  simp only [avgOver_eq_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ q : K ⧸ (rightStab f).subgroupOf K,
      ∑ q' : K' ⧸ N, ((N.index : ℂ)⁻¹) • ((((rightStab f).relIndex K : ℂ)⁻¹) •
        f (x * ((Quotient.out q' : K') : G) * ((Quotient.out q : K) : G))) =
      (((rightStab f).relIndex K : ℂ)⁻¹) • avgSub K' N f x := by
    intro q
    have := avgSub_comp_mul_right_of_normal hNi hN1 (hKK' (Quotient.out q).2) x
    rw [avgSub_eq_sum, avgSub_eq_sum] at this
    rw [avgSub_eq_sum, ← this, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [smul_smul, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, avgSub_eq_sum]
  have hcard : (Fintype.card (K ⧸ (rightStab f).subgroupOf K) : ℂ) = (rightStab f).relIndex K := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hcard, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hf), one_smul, Finset.smul_sum]

end Average2

section Topological

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem relIndex_ne_zero_of_isCompact_of_isOpen {K L : Subgroup G} (hK : IsCompact (K : Set G))
    (hL : IsOpen (L : Set G)) : L.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hopen : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hL.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen (L.subgroupOf K) hopen
  exact Subgroup.index_ne_zero_of_finite

omit [AddCommGroup W] [Module ℂ W] in

theorem avgFinite_of_isOpen {K U : Subgroup G} {f : G → W} (hK : IsCompact (K : Set G))
    (hU : IsOpen (U : Set G)) (hUf : U ≤ rightStab f) : AvgFinite K f :=
  relIndex_ne_zero_of_isCompact_of_isOpen hK (Subgroup.isOpen_mono hUf hU)

end Topological

section Volume

variable {G : Type*} [Group G]

def relVol (K₀ K : Subgroup G) : ℝ := (K₀.relIndex K : ℝ) / (K.relIndex K₀)

theorem relVol_self (K₀ : Subgroup G) : relVol K₀ K₀ = 1 := by
  simp [relVol, Subgroup.relIndex_self]

theorem relVol_pos {K₀ K : Subgroup G} (h₁ : K₀.relIndex K ≠ 0) (h₂ : K.relIndex K₀ ≠ 0) :
    0 < relVol K₀ K :=
  div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero h₁)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero h₂))

theorem relVol_eq_relIndex_mul {K₀ K L : Subgroup G} (hLK : L ≤ K) (hL : L.relIndex K₀ ≠ 0) :
    relVol K₀ K = L.relIndex K * relVol K₀ L := by
  have E1 : K₀.relIndex L * L.relIndex K = (L ⊓ K₀).relIndex (K ⊓ K₀) * K₀.relIndex K := by
    have a := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : L ⊓ K₀ ≤ L) hLK
    have b := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_right K₀ hLK)
      (inf_le_left : K ⊓ K₀ ≤ K)
    rw [Subgroup.inf_relIndex_left] at a
    rw [Subgroup.inf_relIndex_left] at b
    rw [a, ← b]
  have E2 : (L ⊓ K₀).relIndex (K ⊓ K₀) * K.relIndex K₀ = L.relIndex K₀ := by
    have b := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_right K₀ hLK)
      (inf_le_right : K ⊓ K₀ ≤ K₀)
    rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at b
    exact b
  have hc : (L ⊓ K₀).relIndex (K ⊓ K₀) ≠ 0 := fun h => hL (by rw [← E2, h, zero_mul])
  have hK : K.relIndex K₀ ≠ 0 := fun h => hL (by rw [← E2, h, mul_zero])
  unfold relVol
  have hc' : ((L ⊓ K₀).relIndex (K ⊓ K₀) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc
  have hK' : (K.relIndex K₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  have hL' : (L.relIndex K₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL
  have E1' : (K₀.relIndex L : ℝ) * L.relIndex K = (L ⊓ K₀).relIndex (K ⊓ K₀) * K₀.relIndex K := by
    exact_mod_cast E1
  have E2' : ((L ⊓ K₀).relIndex (K ⊓ K₀) : ℝ) * K.relIndex K₀ = L.relIndex K₀ := by
    exact_mod_cast E2
  have key : (L.relIndex K : ℝ) * ((K₀.relIndex L : ℝ) / (L.relIndex K₀)) =
      (K₀.relIndex K : ℝ) / (K.relIndex K₀) := by
    calc (L.relIndex K : ℝ) * ((K₀.relIndex L : ℝ) / (L.relIndex K₀))
        = ((K₀.relIndex L : ℝ) * L.relIndex K) / (L.relIndex K₀) := by ring
      _ = (((L ⊓ K₀).relIndex (K ⊓ K₀) : ℝ) * K₀.relIndex K) /
            (((L ⊓ K₀).relIndex (K ⊓ K₀) : ℝ) * K.relIndex K₀) := by rw [E1', E2']
      _ = (K₀.relIndex K : ℝ) / (K.relIndex K₀) := by
            rw [mul_div_mul_left _ _ hc']
  exact key.symm

theorem relVol_map_conj (g : G) (K₀ K : Subgroup G) :
    relVol (K₀.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) =
      relVol K₀ K := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  unfold relVol
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_map_map_of_injective _ _ hinj]

end Volume

end Parabolic

end GroundTheory.Automorphic
