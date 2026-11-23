import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ClassRefine

open scoped Classical

variable {G : Type*} [Group G] (Q : Subgroup G)

def stabQ (J : Subgroup G) (t : G) : Subgroup Q :=
  (J.comap (MulAut.conj t⁻¹).toMonoidHom).comap Q.subtype

variable {Q}

theorem mem_stabQ {J : Subgroup G} {t : G} {q : Q} : q ∈ stabQ Q J t ↔ t⁻¹ * (q : G) * t ∈ J := by
  rw [stabQ, Subgroup.mem_comap, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]

theorem card_stabQ_eq (J : Subgroup G) (t : G) :
    Nat.card (stabQ Q J t) = Nat.card {q : Q // t⁻¹ * (q : G) * t ∈ J} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabQ)

theorem card_stabQ_left (J : Subgroup G) (x : G) (γ : Q) :
    Nat.card (stabQ Q J ((γ : G) * x)) = Nat.card (stabQ Q J x) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨γ⁻¹ * q * γ, ?_⟩
      invFun := fun q => ⟨γ * q * γ⁻¹, ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem card_stabQ_split {J J' : Subgroup G} (hJ : J' ≤ J) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J)
    (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') (t s : G) (γ₀ : Q) (κ₀ : G) (hκ₀ : κ₀ ∈ J)
    (hs : s = (γ₀ : G) * t * κ₀) :
    Nat.card (stabQ Q J t) =
      (F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j).card * Nat.card (stabQ Q J' s) := by
  have hex : ∀ κ ∈ J, ∃ u, u ∈ F ∧ u⁻¹ * κ ∈ J' := fun κ hκ => (hFu κ hκ).exists
  choose! uF huF hJu using hex
  have huniq : ∀ κ ∈ J, ∀ u ∈ F, u⁻¹ * κ ∈ J' → u = uF κ := fun κ hκ u hu h =>
    (hFu κ hκ).unique ⟨hu, h⟩ ⟨huF κ hκ, hJu κ hκ⟩
  have hSΓ : stabQ Q J' (t * κ₀) ≤ stabQ Q J t := by
    intro q hq
    rw [mem_stabQ] at hq ⊢
    have : κ₀ * ((t * κ₀)⁻¹ * (q : G) * (t * κ₀)) * κ₀⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hκ₀ (hJ hq)) (J.inv_mem hκ₀)
    simpa [mul_assoc] using this
  set Γ := stabQ Q J t with hΓ
  set S := stabQ Q J' (t * κ₀) with hS
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j with hU
  let κf : Γ → G := fun q => t⁻¹ * ((q : Q) : G) * t * κ₀
  have hκ : ∀ q : Γ, κf q ∈ J := fun q => J.mul_mem (mem_stabQ.1 q.2) hκ₀
  have hψ : ∀ q : Γ, uF (κf q) ∈ U := by
    intro q
    rw [hU, Finset.mem_filter]
    refine ⟨huF _ (hκ q), (q : Q) * γ₀⁻¹, ((uF (κf q))⁻¹ * κf q)⁻¹, J'.inv_mem (hJu _ (hκ q)), ?_⟩
    simp only [κf, hs]
    push_cast
    group
  let ψ : Γ → U := fun q => ⟨uF (κf q), hψ q⟩
  have hresp : ∀ a b : Γ, a⁻¹ * b ∈ S.subgroupOf Γ → ψ a = ψ b := by
    intro a b h
    rw [Subgroup.mem_subgroupOf, hS, mem_stabQ] at h
    apply Subtype.ext
    show uF (κf a) = uF (κf b)
    refine huniq (κf b) (hκ b) (uF (κf a)) (huF _ (hκ a)) ?_
    have e : (uF (κf a))⁻¹ * κf b =
        ((uF (κf a))⁻¹ * κf a) * ((t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀)) := by
      simp only [κf]
      push_cast
      group
    rw [e]
    exact J'.mul_mem (hJu _ (hκ a)) h
  let Φ : Γ ⧸ S.subgroupOf Γ → U := Quotient.lift ψ (fun a b h => hresp a b (QuotientGroup.leftRel_apply.1 h))
  have hΦ : ∀ a : Γ, Φ (a : Γ ⧸ S.subgroupOf Γ) = ψ a := fun a => rfl
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hΦ, hΦ] at hxy
      have hab : uF (κf a) = uF (κf b) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hS, mem_stabQ]
      have h1 := hJu _ (hκ a)
      have h2 := hJu _ (hκ b)
      rw [hab] at h1
      have e : (t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀) =
          ((uF (κf b))⁻¹ * κf a)⁻¹ * ((uF (κf b))⁻¹ * κf b) := by
        simp only [κf]
        push_cast
        group
      rw [e]
      exact J'.mul_mem (J'.inv_mem h1) h2
    · rintro ⟨u, hu⟩
      have hu' := hu
      rw [hU, Finset.mem_filter] at hu'
      obtain ⟨huF', q, j, hj, e⟩ := hu'
      have hu_eq : u = t⁻¹ * ((q : G) * ((γ₀ : G) * t * κ₀) * j) := by
        rw [← hs, ← e]; group
      have hmem : t⁻¹ * (((q * γ₀ : Q)) : G) * t = u * j⁻¹ * κ₀⁻¹ := by
        rw [hu_eq]; push_cast; group
      have hqΓ : q * γ₀ ∈ Γ := by
        rw [hΓ, mem_stabQ, hmem]
        exact J.mul_mem (J.mul_mem (hF u huF') (J.inv_mem (hJ hj))) (J.inv_mem hκ₀)
      refine ⟨((⟨q * γ₀, hqΓ⟩ : Γ) : Γ ⧸ S.subgroupOf Γ), ?_⟩
      rw [hΦ]
      apply Subtype.ext
      show uF (κf ⟨q * γ₀, hqΓ⟩) = u
      refine (huniq _ (hκ _) u huF' ?_).symm
      have e2 : u⁻¹ * κf ⟨q * γ₀, hqΓ⟩ = j⁻¹ := by
        show u⁻¹ * (t⁻¹ * (((q * γ₀ : Q)) : G) * t * κ₀) = j⁻¹
        rw [hmem]; group
      rw [e2]
      exact J'.inv_mem hj
  have h1 := Subgroup.card_mul_index (S.subgroupOf Γ)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv, Subgroup.index,
    Nat.card_eq_of_bijective Φ hbij, Nat.card_eq_finsetCard] at h1
  have h2 : Nat.card (stabQ Q J' s) = Nat.card S := by
    rw [hS, hs, mul_assoc]
    exact card_stabQ_left J' (t * κ₀) γ₀
  rw [h2, ← h1, mul_comm]

theorem sum_classReps_refine {J J' : Subgroup G} (hJ : J' ≤ J) {T T' : Finset G}
    (hT : ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Q) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ)
    (hT' : ∀ g : G, ∃! t, t ∈ T' ∧ ∃ (γ : Q) (κ : G), κ ∈ J' ∧ g = (γ : G) * t * κ)
    (φ : G → ℂ) (hφQ : ∀ (γ : Q) g, φ ((γ : G) * g) = φ g) (hφJ : ∀ κ ∈ J', ∀ g, φ (g * κ) = φ g)
    {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J) (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') :
    ∑ t' ∈ T', ((Nat.card (stabQ Q J' t') : ℂ))⁻¹ * φ t' =
      ∑ t ∈ T, ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * ∑ u ∈ F, φ (t * u) := by
  choose! rep hrepT hrep using fun g => (hT' g).exists
  have hrepeq : ∀ g t', t' ∈ T' → ∀ (γ : Q) (κ : G), κ ∈ J' → g = γ * t' * κ → rep g = t' :=
    fun g t' ht' γ κ hκ e => (hT' g).unique ⟨hrepT g, hrep g⟩ ⟨ht', γ, κ, hκ, e⟩
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product' (f := fun t u => ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * φ (t * u)),
    ← Finset.sum_fiberwise_of_maps_to (s := T ×ˢ F) (t := T') (g := fun p => rep (p.1 * p.2))
      (fun p _ => hrepT _)]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  obtain ⟨t₀, ht₀, γ₀, κ₀, hκ₀, e₀⟩ := (hT t').exists
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t₀ * u = q * t' * j with hU
  have hfib : (T ×ˢ F).filter (fun p => rep (p.1 * p.2) = t') = {t₀} ×ˢ U := by
    ext ⟨a, u⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, hU]
    constructor
    · rintro ⟨⟨ha, hu⟩, hp⟩
      obtain ⟨γ, κ, hκ, e⟩ := hrep (a * u)
      rw [hp] at e
      have ha0 : a = t₀ := by
        refine (hT a).unique ⟨ha, 1, 1, J.one_mem, by simp⟩
          ⟨ht₀, γ * γ₀, κ₀ * κ * u⁻¹, J.mul_mem (J.mul_mem hκ₀ (hJ hκ)) (J.inv_mem (hF u hu)), ?_⟩
        have ea : a = a * u * u⁻¹ := by group
        rw [ea, e, e₀]
        push_cast
        group
      subst ha0
      exact ⟨rfl, hu, γ, κ, hκ, e⟩
    · rintro ⟨rfl, hu, q, j, hj, e⟩
      exact ⟨⟨ht₀, hu⟩, hrepeq _ t' ht' q j hj e⟩
  rw [hfib, Finset.sum_product, Finset.sum_singleton]
  have hval : ∀ u ∈ U, ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ (t₀ * u) =
      ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ t' := by
    intro u hu
    rw [hU, Finset.mem_filter] at hu
    obtain ⟨_, q, j, hj, e⟩ := hu
    rw [e, mul_assoc, hφQ, hφJ j hj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_stabQ_split hJ hF hFu t₀ t' γ₀ κ₀ hκ₀ e₀]
  have hne : U.card ≠ 0 := by
    obtain ⟨u, hu, hj⟩ := (hFu κ₀ hκ₀).exists
    refine Finset.card_ne_zero_of_mem (s := U) (a := u) ?_
    rw [hU, Finset.mem_filter]
    refine ⟨hu, γ₀⁻¹, (u⁻¹ * κ₀)⁻¹, J'.inv_mem hj, ?_⟩
    rw [e₀]
    push_cast
    group
  have hc : (U.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  rw [nsmul_eq_mul, Nat.cast_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem classSum_smaller_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), IsInvForm a β → ∀ (J J' : Subgroup (GAf L n)) (T T' : Finset (GAf L n)), IsBounded J → J' ≤ J → J'.relIndex J ≠ 0 → IsClassReps J T → IsClassReps J' T' → ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, (∀ κ ∈ J', ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g)) → ∀ F : Finset (GAf L n), (∀ κ ∈ F, κ ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') → classSum a β J' T' f f' = ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * ∑ u ∈ F, β (f (t * u)) (f' (t * u)) := by
  intro L _ _ _ n a β hβ J J' T T' _ hJ _ hT hT' f hf f' hf' hinv F hF hFu
  have key := sum_classReps_refine (Q := GQ L n) hJ hT hT' (fun g => β (f g) (f' g))
    (fun γ g => by rw [hf.1 γ g, hf'.1 γ g, hβ.2.2]) (fun κ hκ g => hinv κ hκ g) hF hFu
  simp only [card_stabQ_eq] at key
  exact key

end GlobalTheory.ClassRefine

end
