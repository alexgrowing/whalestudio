import Mathlib

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK

variable {K : Type} [Field K] [NumberField K]

theorem exists_prim {m : ℕ} (c : Fin m → 𝓞 K) (hc : c ≠ 0) (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ t : K, (∀ i, ∃ o : 𝓞 K, (o : K) = t * (c i : K)) ∧ ∃ i, ∀ o : 𝓞 K, (o : K) = t * (c i : K) → o ∉ 𝔭 := by
  classical
  obtain ⟨𝔪, h𝔪, hp𝔪⟩ := Ideal.exists_le_maximal 𝔭 h𝔭
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  have hJ0 : Ideal.span (Set.range c) ≠ ⊥ := by
    intro h
    have hmem : c j ∈ Ideal.span (Set.range c) := Ideal.subset_span ⟨j, rfl⟩
    rw [h, Ideal.mem_bot] at hmem
    exact hj hmem
  have hJF : ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ0
  by_contra H
  push_neg at H
  have hle : ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤
      ((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mul_le]
    intro x hx t ht
    rw [FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [FractionalIdeal.mem_inv_iff hJF] at ht
    have hint_r : ∀ i, ∃ o : 𝓞 K, (o : K) = t * (c i : K) := by
      intro i
      have hci : algebraMap (𝓞 K) K (c i) ∈
          ((Ideal.span (Set.range c) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨c i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
      have h1 := ht _ hci
      rw [FractionalIdeal.mem_one_iff] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, ho⟩
    have hS : Ideal.span (Set.range c) ≤ Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) K t)
        (((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨o, ho, hop⟩ := H t hint_r i
      show (LinearMap.toSpanSingleton (𝓞 K) K t) (c i) ∈
        (((𝔪 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]
      refine ⟨o, hp𝔪 hop, ?_⟩
      rw [Algebra.smul_def, mul_comm]
      exact ho
    have hyS := hS hy
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe,
      Algebra.smul_def] at hyS
    exact hyS
  first
  | rw [mul_inv_cancel₀ hJF] at hle
  | rw [FractionalIdeal.mul_inv_cancel hJF] at hle
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at hle
  exact h𝔪.ne_top (top_le_iff.mp hle)

section Bound

variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

private theorem absNorm_eq_card_quotient (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  | simp [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  | rfl

private theorem finite_quotient_of_ne_bot (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : Finite (𝓞 K ⧸ I) := by
  first
  | exact Nat.finite_of_card_ne_zero (by
      rw [← absNorm_eq_card_quotient]; exact fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  | exact Ideal.finiteQuotientOfFreeOfNeBot I hI

private theorem ringOfIntegers_coe_injective : Function.Injective (fun x : 𝓞 K => (x : K)) := by
  first
  | exact RingOfIntegers.coe_injective
  | exact Subtype.val_injective
  | exact FaithfulSMul.algebraMap_injective (𝓞 K) K
  | exact IsFractionRing.injective (𝓞 K) K

private theorem card_le_card_pow_of_not_linearIndependent {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (n : ℕ) (h : ∀ v : Fin (n + 1) → V, LinearIndependent k v → False) :
    Nat.card V ≤ Nat.card k ^ n := by
  classical
  have hd : Module.finrank k V ≤ n := by
    by_contra hlt
    push_neg at hlt
    exact h (Module.finBasis k V ∘ Fin.castLE hlt)
      ((Module.finBasis k V).linearIndependent.comp _ (Fin.castLE_injective hlt))
  rw [Nat.card_congr (Module.finBasis k V).equivFun.toEquiv, Nat.card_fun]
  have hc : Nat.card (Fin (Module.finrank k V)) = Module.finrank k V := by simp
  rw [hc]
  exact Nat.pow_le_pow_right Nat.card_pos hd

theorem card_quot_le (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsMaximal] (n : ℕ)
    (hdep : ∀ y : Fin (n + 1) → M, ∃ c : Fin (n + 1) → 𝓞 K, c ≠ 0 ∧ ∑ i, c i • y i = 0) :
    Nat.card (M ⧸ 𝔭 • (⊤ : Submodule (𝓞 K) M)) ≤ Nat.card (𝓞 K ⧸ 𝔭) ^ n := by
  classical
  letI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hbot : 𝔭 ≠ ⊥ := by
    first
    | exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField K)
    | exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 NumberField.RingOfIntegers.not_isField
  haveI : Finite (𝓞 K ⧸ 𝔭) := finite_quotient_of_ne_bot 𝔭 hbot
  haveI : Module.Finite (𝓞 K ⧸ 𝔭) (M ⧸ 𝔭 • (⊤ : Submodule (𝓞 K) M)) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  refine card_le_card_pow_of_not_linearIndependent n ?_
  intro v hv
  choose y hy using fun i => Submodule.Quotient.mk_surjective (𝔭 • (⊤ : Submodule (𝓞 K) M)) (v i)
  obtain ⟨c, hc0, hcs⟩ := hdep y
  obtain ⟨t, ht, i₀, hi₀⟩ := exists_prim c hc0 𝔭 h𝔭.ne_top
  choose o ho using ht
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc0 (funext h)
  have hoc : ∀ i, o i * c j = o j * c i := by
    intro i
    apply ringOfIntegers_coe_injective
    first
    | (show (o i : K) * (c j : K) = (o j : K) * (c i : K)
       rw [ho, ho]; ring)
    | (simp only [map_mul]
       rw [ho, ho]; ring)
    | (push_cast
       rw [ho, ho]; ring)
  have hsum0 : ∑ i, o i • y i = 0 := by
    have h1 : c j • ∑ i, o i • y i = o j • ∑ i, c i • y i := by
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, mul_comm (c j), hoc i]
    rw [hcs, smul_zero] at h1
    exact (smul_eq_zero.mp h1).resolve_left hj
  have h2 : ∑ i, (Ideal.Quotient.mk 𝔭 (o i)) • v i = 0 := by
    have h3 := congrArg (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) M))) hsum0
    rw [map_sum, map_zero] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy i, Submodule.mkQ_apply, Submodule.Quotient.mk_smul]
    first
    | rfl
    | (rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul])
    | exact algebraMap_smul _ _ _
  have h4 := (Fintype.linearIndependent_iff.mp hv) _ h2 i₀
  exact hi₀ (o i₀) (ho i₀) (Ideal.Quotient.eq_zero_iff_mem.mp h4)

end Bound

section Principal

open scoped Pointwise

variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

theorem smul_toAddSubgroup (π : 𝓞 K) (N : Submodule (𝓞 K) M) :
    (Ideal.span {π} • N).toAddSubgroup = N.toAddSubgroup.map (DistribSMul.toAddMonoidHom M π) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, AddSubgroup.mem_map]
  first
  | simp
  | exact Iff.rfl

theorem smul_inj (π : 𝓞 K) (hπ : π ≠ 0) : Function.Injective (DistribSMul.toAddMonoidHom M π) := by
  intro x y h
  exact smul_right_injective M hπ (by simpa using h)

private theorem card_quotient_eq_index {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) : Nat.card (N ⧸ S) = S.toAddSubgroup.index := by
  first
  | rfl
  | exact (Submodule.cardQuot_apply S).symm

private theorem mem_smul_univ_iff_coe_mem_smul (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) (x : N) :
    x ∈ I • (⊤ : Submodule (𝓞 K) N) ↔ (x : M) ∈ I • N := by
  first
  | exact Submodule.mem_smul_top_iff N x
  | (have e : Submodule.map N.subtype (I • (⊤ : Submodule (𝓞 K) N)) = I • N := by
       rw [Submodule.map_smul'', Submodule.map_subtype_top]
     rw [← e, Submodule.mem_map]
     constructor
     · intro h
       exact ⟨x, h, rfl⟩
     · rintro ⟨y, hy, hxy⟩
       have hyx : y = x := Subtype.ext hxy
       rwa [hyx] at hy)

private theorem relIndex_smul_eq_card_quotient_smul (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) :
    (I • N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ I • (⊤ : Submodule (𝓞 K) N)) := by
  have hmap : AddSubgroup.map N.subtype.toAddMonoidHom ⊤ = N.toAddSubgroup := by
    ext x
    first
    | simp
    | (constructor
       · rintro ⟨y, -, rfl⟩
         exact y.2
       · intro hx
         exact ⟨⟨x, hx⟩, trivial, rfl⟩)
  have hc : AddSubgroup.comap N.subtype.toAddMonoidHom (I • N).toAddSubgroup =
      (I • (⊤ : Submodule (𝓞 K) N)).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, mem_smul_univ_iff_coe_mem_smul]
    first
    | rfl
    | simp
  rw [← hmap, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hc, card_quotient_eq_index]

theorem relIndex_smul_ne_zero (N : Submodule (𝓞 K) M) (hN : N.FG) (d : 𝓞 K) (hd : d ≠ 0) :
    (Ideal.span {d} • N).toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
  rw [relIndex_smul_eq_card_quotient_smul]
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.mpr hN
  have hb : Ideal.span {d} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Finite (𝓞 K ⧸ Ideal.span {d}) := finite_quotient_of_ne_bot _ hb
  haveI : Module.Finite (𝓞 K ⧸ Ideal.span {d}) (N ⧸ Ideal.span {d} • (⊤ : Submodule (𝓞 K) N)) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  haveI : Finite (N ⧸ Ideal.span {d} • (⊤ : Submodule (𝓞 K) N)) :=
    Module.finite_of_finite (𝓞 K ⧸ Ideal.span {d})
  exact Nat.card_pos.ne'

private theorem absNorm_eq_index_dual_family_counting (I : Ideal (𝓞 K)) : Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [absNorm_eq_card_quotient, card_quotient_eq_index]

private theorem relIndex_mul_relIndex_of_le_of_le {G : Type*} [AddGroup G] {H J L : AddSubgroup G} (h1 : H ≤ J) (h2 : J ≤ L) :
    H.relIndex J * J.relIndex L = H.relIndex L := by
  first
  | exact AddSubgroup.relIndex_mul_relIndex H J L h1 h2
  | exact AddSubgroup.relIndex_mul_relIndex h1 h2

theorem relIndex_principal (N : Submodule (𝓞 K) M) (hN : N.FG) (n : ℕ) (ι : (Fin n → 𝓞 K) →ₗ[𝓞 K] M)
    (hι : Function.Injective ι) (hιN : LinearMap.range ι ≤ N) (d : 𝓞 K) (hd : d ≠ 0)
    (hdN : Ideal.span {d} • N ≤ LinearMap.range ι) (π : 𝓞 K) (hπ : π ≠ 0) :
    (Ideal.span {π} • N).toAddSubgroup.relIndex N.toAddSubgroup = (Algebra.norm ℤ π).natAbs ^ n := by
  classical
  have hCB : (LinearMap.range ι).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => hιN hx
  have hDC : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup ≤ (LinearMap.range ι).toAddSubgroup :=
    fun x hx => Submodule.smul_le_right hx
  have hDA : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup ≤ (Ideal.span {π} • N).toAddSubgroup := by
    intro x hx
    first
    | exact Submodule.smul_mono le_rfl hιN hx
    | exact Submodule.smul_mono_right _ hιN hx
    | exact Submodule.smul_mono_right hιN hx
  have hAB : (Ideal.span {π} • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have e1 := relIndex_mul_relIndex_of_le_of_le hDC hCB
  have e2 := relIndex_mul_relIndex_of_le_of_le hDA hAB
  have e3 : (Ideal.span {π} • LinearMap.range ι).toAddSubgroup.relIndex (Ideal.span {π} • N).toAddSubgroup =
      (LinearMap.range ι).toAddSubgroup.relIndex N.toAddSubgroup := by
    rw [smul_toAddSubgroup π (LinearMap.range ι), smul_toAddSubgroup π N,
      ← AddSubgroup.relIndex_comap]
    first
    | rw [AddSubgroup.comap_map_eq_self_of_injective (smul_inj π hπ)]
    | (congr 1
       ext x
       rw [AddSubgroup.mem_comap, AddSubgroup.mem_map]
       constructor
       · rintro ⟨y, hy, hyx⟩
         rwa [← smul_inj π hπ hyx]
       · intro hx
         exact ⟨x, hx, rfl⟩)
  have hCB0 : (LinearMap.range ι).toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
    have hdC : (Ideal.span {d} • N).toAddSubgroup ≤ (LinearMap.range ι).toAddSubgroup := fun x hx => hdN hx
    have e4 := relIndex_mul_relIndex_of_le_of_le hdC hCB
    intro h0
    rw [h0, mul_zero] at e4
    exact relIndex_smul_ne_zero N hN d hd e4.symm
  have hAB_eq : (Ideal.span {π} • N).toAddSubgroup.relIndex N.toAddSubgroup =
      (Ideal.span {π} • LinearMap.range ι).toAddSubgroup.relIndex (LinearMap.range ι).toAddSubgroup := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hCB0)
    rw [e1, ← e2, e3, mul_comm]
  rw [hAB_eq]
  have hmap : AddSubgroup.map ι.toAddMonoidHom ⊤ = (LinearMap.range ι).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  have hcomap : AddSubgroup.comap ι.toAddMonoidHom (Ideal.span {π} • LinearMap.range ι).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun _ : Fin n => (Ideal.span {π}).toAddSubgroup) := by
    ext x
    show (ι x ∈ Ideal.span {π} • LinearMap.range ι) ↔ ∀ i ∈ (Set.univ : Set (Fin n)), x i ∈ Ideal.span {π}
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz1, hz⟩ i -
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz1
      have hyx : π • y = x := hι (by rw [map_smul]; exact hz)
      rw [← hyx, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
    · intro hx
      choose y hy using fun i => Ideal.mem_span_singleton'.mp (hx i (Set.mem_univ i))
      refine ⟨ι y, LinearMap.mem_range_self ι y, ?_⟩
      rw [← map_smul]
      congr 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact hy i
  rw [← hmap, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hcomap, AddSubgroup.index_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← absNorm_eq_index_dual_family_counting, Ideal.absNorm_span_singleton]

end Principal

section General

variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

def HDep (n : ℕ) (N : Submodule (𝓞 K) M) : Prop :=
  ∀ y : Fin (n + 1) → M, (∀ i, y i ∈ N) → ∃ c : Fin (n + 1) → 𝓞 K, c ≠ 0 ∧ ∑ i, c i • y i = 0

theorem HDep.mono {n : ℕ} {N N' : Submodule (𝓞 K) M} (h : HDep n N) (hle : N' ≤ N) : HDep n N' := by
  intro y hy
  exact h y (fun i => hle (hy i))

theorem relIndex_eq_card (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) :
    (I • N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ I • (⊤ : Submodule (𝓞 K) N)) :=
  relIndex_smul_eq_card_quotient_smul I N

theorem fg_smul (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) (hN : N.FG) : (I • N).FG := by
  first
  | exact Submodule.FG.smul (IsNoetherian.noetherian I) hN
  | exact hN.smul (IsNoetherian.noetherian I)
  | (haveI : IsNoetherian (𝓞 K) N := isNoetherian_of_fg_of_noetherian N hN
     have e : Submodule.map N.subtype (I • (⊤ : Submodule (𝓞 K) N)) = I • N := by
       rw [Submodule.map_smul'', Submodule.map_subtype_top]
     rw [← e]
     exact (IsNoetherian.noetherian _).map _)

theorem relIndex_prime_le (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal] (n : ℕ) (N : Submodule (𝓞 K) M) (hN : N.FG)
    (hD : HDep n N) : (𝔭 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔭 ^ n := by
  haveI : Module.Finite (𝓞 K) N := Module.Finite.iff_fg.mpr hN
  haveI : NoZeroSMulDivisors (𝓞 K) N := ⟨fun {c x} h => by
    have h' : c • (x : M) = 0 := by simpa using congrArg Subtype.val h
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (Subtype.ext h0)⟩
  have hdep : ∀ y : Fin (n + 1) → N, ∃ c : Fin (n + 1) → 𝓞 K, c ≠ 0 ∧ ∑ i, c i • y i = 0 := by
    intro y
    obtain ⟨c, hc, hs⟩ := hD (fun i => (y i : M)) (fun i => (y i).2)
    refine ⟨c, hc, ?_⟩
    apply Subtype.ext
    simpa using hs
  rw [relIndex_eq_card, absNorm_eq_card_quotient]
  exact card_quot_le 𝔭 n hdep

private theorem ideal_mul_smul_submodule (I J : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) : (I * J) • N = I • J • N := by
  first
  | exact Submodule.mul_smul I J N
  | (rw [← Ideal.smul_eq_mul]; exact Submodule.smul_assoc I J N)
  | exact mul_smul I J N

private theorem relIndex_smul_le_absNorm_pow_of_hDep (n k : ℕ) : ∀ (𝔞 : Ideal (𝓞 K)), Ideal.absNorm 𝔞 ≤ k → 𝔞 ≠ ⊥ →
    ∀ (N : Submodule (𝓞 K) M), N.FG → HDep n N →
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  induction k with
  | zero =>
    intro 𝔞 hk h𝔞
    exact absurd (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp hk)) h𝔞
  | succ k ih =>
    intro 𝔞 hk h𝔞 N hN hD
    by_cases htop : 𝔞 = ⊤
    · subst htop
      rw [Submodule.top_smul, AddSubgroup.relIndex_self]
      exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔞))
    · obtain ⟨𝔭, h𝔭max, h𝔞𝔭⟩ := Ideal.exists_le_maximal 𝔞 htop
      haveI := h𝔭max
      obtain ⟨𝔟, rfl⟩ := Ideal.dvd_iff_le.mpr h𝔞𝔭
      have h𝔭0 : 𝔭 ≠ ⊥ := by
        rintro rfl
        apply h𝔞
        simp
      have h𝔟0 : 𝔟 ≠ ⊥ := by
        rintro rfl
        apply h𝔞
        simp
      rw [map_mul] at hk ⊢
      have hp2 : 2 ≤ Ideal.absNorm 𝔭 := by
        have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔭0
        have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]; exact h𝔭max.ne_top
        omega
      have hb0 : Ideal.absNorm 𝔟 ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔟0
      have hbk : Ideal.absNorm 𝔟 ≤ k := by
        have hb1 : 1 ≤ Ideal.absNorm 𝔟 := Nat.pos_of_ne_zero hb0
        nlinarith
      rw [ideal_mul_smul_submodule 𝔭 𝔟 N]
      have hle1 : (𝔭 • 𝔟 • N).toAddSubgroup ≤ (𝔟 • N).toAddSubgroup := fun x hx => Submodule.smul_le_right hx
      have hle2 : (𝔟 • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
      rw [← relIndex_mul_relIndex_of_le_of_le hle1 hle2, mul_pow]
      exact Nat.mul_le_mul
        (relIndex_prime_le 𝔭 n (𝔟 • N) (fg_smul 𝔟 N hN) (hD.mono Submodule.smul_le_right))
        (ih 𝔟 hbk h𝔟0 N hN hD)

theorem relIndex_le (n : ℕ) : ∀ (𝔞 : Ideal (𝓞 K)), 𝔞 ≠ ⊥ → ∀ (N : Submodule (𝓞 K) M), N.FG → HDep n N →
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  intro 𝔞 h𝔞 N hN hD
  exact relIndex_smul_le_absNorm_pow_of_hDep n _ 𝔞 le_rfl h𝔞 N hN hD

theorem relIndex_eq (n : ℕ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (N : Submodule (𝓞 K) M) (hN : N.FG) (hD : HDep n N)
    (ι : (Fin n → 𝓞 K) →ₗ[𝓞 K] M) (hι : Function.Injective ι) (hιN : LinearMap.range ι ≤ N) (d : 𝓞 K) (hd : d ≠ 0)
    (hdN : Ideal.span {d} • N ≤ LinearMap.range ι) :
    (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup = Ideal.absNorm 𝔞 ^ n := by
  obtain ⟨π, hπ𝔞, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ𝔞)
  have h𝔟' : Ideal.span {π} = 𝔟 * 𝔞 := by rw [h𝔟, mul_comm]
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_mul, Ideal.span_singleton_eq_bot] at h𝔟'
    exact hπ0 h𝔟'
  have hN' : (𝔞 • N).FG := fg_smul 𝔞 N hN
  have hD' : HDep n (𝔞 • N) := hD.mono Submodule.smul_le_right
  have h1 := relIndex_le n 𝔞 h𝔞 N hN hD
  have h2 := relIndex_le n 𝔟 h𝔟0 (𝔞 • N) hN' hD'
  have hle1 : (𝔟 • 𝔞 • N).toAddSubgroup ≤ (𝔞 • N).toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have hle2 : (𝔞 • N).toAddSubgroup ≤ N.toAddSubgroup := fun x hx => Submodule.smul_le_right hx
  have hprod : (𝔟 • 𝔞 • N).toAddSubgroup.relIndex (𝔞 • N).toAddSubgroup *
      (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup = Ideal.absNorm 𝔟 ^ n * Ideal.absNorm 𝔞 ^ n := by
    rw [relIndex_mul_relIndex_of_le_of_le hle1 hle2, ← ideal_mul_smul_submodule, ← h𝔟',
      relIndex_principal N hN n ι hι hιN d hd hdN π hπ0, ← Ideal.absNorm_span_singleton, h𝔟',
      map_mul, mul_pow]
  have hB : 0 < Ideal.absNorm 𝔟 ^ n :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔟0)) n
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have hlt2 : (𝔟 • 𝔞 • N).toAddSubgroup.relIndex (𝔞 • N).toAddSubgroup *
      (𝔞 • N).toAddSubgroup.relIndex N.toAddSubgroup < Ideal.absNorm 𝔟 ^ n * Ideal.absNorm 𝔞 ^ n := by
    first
    | exact lt_of_le_of_lt (Nat.mul_le_mul_right _ h2) (Nat.mul_lt_mul_of_pos_left hlt hB)
    | nlinarith
  exact absurd hprod (ne_of_lt hlt2)

end General

end Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
