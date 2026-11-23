import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex

open GlobalTheory.LKCount

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

noncomputable def foldMap (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G)
    (p : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :
    {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) //
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y} :=
  ⟨DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y), by
    obtain ⟨g, k, hg, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    rw [he, DoubleCoset.eq]
    refine ⟨(g * ((Quotient.out p : T) : G))⁻¹, T.inv_mem (T.mul_mem (hΓT hg) (Quotient.out p).2),
      k⁻¹, K.inv_mem hk, by group⟩⟩

end GlobalTheory.ConjugateFold

namespace GlobalTheory.ConjugateFold

variable {G : Type} [Group G]

end GlobalTheory.ConjugateFold

namespace GlobalTheory

variable {G : Type} [Group G] in
private lemma mem_map_conj_iff_inv_mul_mul_mem' (K : Subgroup G) (a x : G) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

variable {G : Type} [Group G] in
private lemma foldMap_bijective' (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (y : G) :
    Function.Bijective (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y) := by
  constructor
  · intro p p' h
    have h' : DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) =
        DoubleCoset.mk Γ' K (((Quotient.out p' : T) : G) * y) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, he⟩ := (DoubleCoset.eq Γ' K _ _).1 h'
    have hmem : y * k * y⁻¹ = ((Quotient.out p : T) : G)⁻¹ * γ⁻¹ * ((Quotient.out p' : T) : G) := by
      rw [eq_mul_inv_of_mul_eq he]; group
    have hT : y * k * y⁻¹ ∈ T := by
      rw [hmem]
      exact T.mul_mem (T.mul_mem (T.inv_mem (Quotient.out p).2) (T.inv_mem (hΓT hγ))) (Quotient.out p').2
    rw [← DoubleCoset.out_eq' _ _ p, ← DoubleCoset.out_eq' _ _ p', DoubleCoset.eq]
    refine ⟨⟨γ, hΓT hγ⟩, by rw [Subgroup.mem_subgroupOf]; exact hγ, ⟨y * k * y⁻¹, hT⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem']
      refine ⟨hT, ?_⟩
      rw [show y⁻¹ * (y * k * y⁻¹) * y = k by group]
      exact hk
    · apply Subtype.ext
      push_cast
      rw [eq_mul_inv_of_mul_eq he]
      group
  · rintro ⟨q, hq⟩
    obtain ⟨t, ht, k, hk, hqe⟩ := (DoubleCoset.eq T K _ _).1 hq.symm
    refine ⟨DoubleCoset.mk (Γ'.subgroupOf T) ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T)
      ⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    change DoubleCoset.mk Γ' K (((Quotient.out (DoubleCoset.mk (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩) : T) : G) * y) = q
    obtain ⟨γ, h, hγ, hh, hout⟩ := DoubleCoset.mk_out_eq_mul (Γ'.subgroupOf T)
      ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T) ⟨t, ht⟩
    rw [hout, ← DoubleCoset.out_eq' Γ' K q, DoubleCoset.eq]
    rw [Subgroup.mem_subgroupOf] at hγ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem'] at hh
    refine ⟨(γ : G)⁻¹, Γ'.inv_mem hγ, (y⁻¹ * h * y)⁻¹ * k, K.mul_mem (K.inv_mem hh.2) hk, ?_⟩
    rw [hqe]
    push_cast
    group

variable {G : Type} [Group G] in
private lemma card_subgroupOf_inf_map_conj_eq (Γ' T K : Subgroup G) (hΓT : Γ' ≤ T) (t : T) (y : G) :
    Nat.card (Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom : Subgroup T) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom : Subgroup G) := by
  set S : Subgroup T := Γ'.subgroupOf T ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj t).toMonoidHom
  have e : S.map T.subtype = Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', Subgroup.mem_map]
    have hconj : ∀ s : T, (((MulAut.conj t).symm s : T) : G) = (t : G)⁻¹ * s * t := by
      intro s
      rw [MulAut.conj_symm_apply]
      push_cast
      rfl
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj] at hs
      refine ⟨hs.1, ?_⟩
      rw [show ((t : G) * y)⁻¹ * (T.subtype s) * ((t : G) * y) = y⁻¹ * ((t : G)⁻¹ * s * t) * y by
        simp only [Subgroup.coe_subtype]; group]
      exact hs.2.2
    · rintro ⟨hx, hxK⟩
      refine ⟨⟨x, hΓT hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf, mem_map_conj_iff_inv_mul_mul_mem', hconj]
      refine ⟨hx, T.mul_mem (T.mul_mem (T.inv_mem t.2) (hΓT hx)) t.2, ?_⟩
      rw [show y⁻¹ * ((t : G)⁻¹ * x * t) * y = ((t : G) * y)⁻¹ * x * ((t : G) * y) by group]
      exact hxK
  rw [← e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).toEquiv

variable {G : Type} [Group G] in
private lemma card_inf_map_conj_mul_mul_eq (Γ' K : Subgroup G) {γ k : G} (hγ : γ ∈ Γ') (hk : k ∈ K) (a : G) :
    Nat.card (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom : Subgroup G) := by
  have e : (Γ' ⊓ K.map (MulAut.conj (γ * a * k)).toMonoidHom : Subgroup G) =
      (Γ' ⊓ K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h1 : (γ * a * k)⁻¹ * x * (γ * a * k) = k⁻¹ * (a⁻¹ * (γ⁻¹ * x * γ) * a) * k := by group
    rw [h1, Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk),
      Subgroup.mul_mem_cancel_right Γ' hγ, Subgroup.mul_mem_cancel_left Γ' (Γ'.inv_mem hγ)]
  rw [e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj γ).injective).toEquiv.symm

theorem _root_.GlobalTheory.finsum_fold_intermediate : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((_root_.GlobalTheory.LKCount.massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  intro G _ Γ' T K F hΓT hF _ hfin
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) =>
      ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
        F (Quotient.out q)).Finite :=
    hfin.subset fun q hq => right_ne_zero_of_mul hq
  refine (_root_.GlobalTheory.finsum_fiberwise_of_finite_support (A := DoubleCoset.Quotient (Γ' : Set G) (K : Set G))
    (B := DoubleCoset.Quotient (T : Set G) (K : Set G))
    (fun q => DoubleCoset.mk T K (Quotient.out q)) _ hsupp).trans (finsum_congr fun y' => ?_)
  set y := Quotient.out y'
  have hy' : DoubleCoset.mk T K y = y' := DoubleCoset.out_eq' T K y'
  have hfib : ∀ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      DoubleCoset.mk T K (Quotient.out q) = DoubleCoset.mk T K y → F (Quotient.out q) = F y := by
    intro q hq
    obtain ⟨t, ht, k, hk, hqe⟩ := (DoubleCoset.eq T K _ _).1 hq.symm
    rw [hqe, hF t ht y k hk]
  let e : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T) →
      {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) // DoubleCoset.mk T K (Quotient.out q) = y'} :=
    fun p => ⟨(_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).1,
      (_root_.GlobalTheory.ConjugateFold.foldMap Γ' T K hΓT y p).2.trans hy'⟩
  have hb := foldMap_bijective' Γ' T K hΓT y
  have he : Function.Bijective e := by
    constructor
    · intro p p' h
      have h' := congrArg Subtype.val h
      exact hb.1 (Subtype.ext h')
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp⟩ := hb.2 ⟨q, hq.trans hy'.symm⟩
      have hp' := congrArg Subtype.val hp
      exact ⟨p, Subtype.ext hp'⟩
  rw [← finsum_eq_of_bijective e he (fun _ => rfl)]
  have hterm : ∀ p, ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out (e p).1)).toMonoidHom :
      Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out (e p).1) =
      ((Nat.card ((Γ'.subgroupOf T) ⊓ ((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T).map
        (MulAut.conj (Quotient.out p)).toMonoidHom : Subgroup T) : ℕ) : ℂ)⁻¹ * F y := by
    intro p
    obtain ⟨γ, k, hγ, hk, hg⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out p : T) : G) * y)
    have hval : (e p).1 = DoubleCoset.mk Γ' K (((Quotient.out p : T) : G) * y) := rfl
    rw [card_subgroupOf_inf_map_conj_eq Γ' T K hΓT, hval, hg, card_inf_map_conj_mul_mul_eq Γ' K hγ hk,
      show γ * (((Quotient.out p : T) : G) * y) * k = (γ * ((Quotient.out p : T) : G)) * y * k by group,
      hF _ (T.mul_mem (hΓT hγ) (Quotient.out p).2) y k hk]
  rw [finsum_congr hterm]
  by_cases hFy : F y = 0
  · simp [hFy]
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} :=
    hfin.to_subtype
  haveI : Finite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T)) :=
    Finite.of_injective
      (β := {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0})
      (fun p => ⟨(e p).1, by
        show F (Quotient.out (e p).1) ≠ 0
        rw [hfib _ ((e p).2.trans hy'.symm)]
        exact hFy⟩)
      (fun p p' h => by
        have h' := congrArg Subtype.val h
        exact he.1 (Subtype.ext h'))
  letI := Fintype.ofFinite (DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ K.map (MulAut.conj y).toMonoidHom).subgroupOf T : Subgroup T) : Set T))
  unfold _root_.GlobalTheory.LKCount.massC
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_mul, Rat.cast_sum]
  simp

end GlobalTheory
