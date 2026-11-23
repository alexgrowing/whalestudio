import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnitStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem finsum_mem_finset_sum_comm {α β : Type} (s : Set α) (P : Finset β) (f : β → α → ℚ)
    (hf : ∀ p ∈ P, (s ∩ Function.support (f p)).Finite) :
    ∑ᶠ x ∈ s, ∑ p ∈ P, f p x = ∑ p ∈ P, ∑ᶠ x ∈ s, f p x := by
  classical
  have hU : (⋃ p ∈ (P : Set β), s ∩ Function.support (f p)).Finite :=
    Set.Finite.biUnion P.finite_toSet fun p hp => hf p (Finset.mem_coe.1 hp)
  have key : ∀ g : α → ℚ, (∀ x ∈ s, g x ≠ 0 → x ∈ ⋃ p ∈ (P : Set β), s ∩ Function.support (f p)) →
      ∑ᶠ x ∈ s, g x = ∑ x ∈ hU.toFinset, g x := by
    intro g hg
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset]
    constructor
    · rintro ⟨hx, hgx⟩; exact ⟨hg x hx hgx, hgx⟩
    · rintro ⟨hx, hgx⟩
      obtain ⟨p, _, hxs, _⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨hxs, hgx⟩
  rw [key]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => (key _ ?_).symm
    intro x hx h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, h⟩
  · intro x hx h
    obtain ⟨p, hp, hpx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hp, hx, hpx⟩

theorem HH_eq_alternating_GG : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u →
    HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  intro K B ι _ _ e π S hL hF I hI u hu
  have hPlus : ∀ J ⊆ S, B.Plus (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ B.Plus (fun a b ha hb => ⟨ha.1.mul hb.1, by rw [map_mul, ha.2, hb.2]⟩)
      ⟨isUnit_one, map_one _⟩ (fun j hj => (hF.2 j (hJ hj)).1)
  have heta1 : K.eta 1 = 1 := by
    have h := eta_mul (K := K) (x := 1) (y := 1) one_ne_zero one_ne_zero
    have h2 := eta_sq (K := K) 1
    rw [mul_one] at h
    rw [← h] at h2
    exact h2
  have heta : ∀ J : Finset ι, J ⊆ S → K.eta (Algebra.norm K.E (∏ j ∈ J, π j)) = (-1 : ℚ) ^ J.card := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro _; simp [heta1]
    | insert a J ha ih =>
      intro hJ
      have haS : a ∈ S := hJ (Finset.mem_insert_self a J)
      have hJS : J ⊆ S := (Finset.subset_insert a J).trans hJ
      rw [Finset.prod_insert ha, map_mul,
        eta_mul ((hF.2 a haS).1.1.map (Algebra.norm K.E)).ne_zero
          ((hPlus J hJS).1.map (Algebra.norm K.E)).ne_zero,
        ih hJS, (hF.2 a haS).2.2, Finset.card_insert_of_notMem ha, pow_succ]
      ring
  have hterm0 : ∀ w s M, term B π ∅ ∅ w s M = indM B M w * indD B M s := by
    intro w s M; simp [term, dlt]
  have hHG : ∀ v, HH B π ∅ ∅ v 1 = B.GG v := by
    intro v
    unfold HH InvAlg.GG
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun M => ?_
    have hD : InDual B 1 M ↔ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range := by
      simp only [InDual, one_mul]
    simp only [Set.indicator, Set.mem_setOf_eq, hterm0, indM, indD, ← hD]
    by_cases h1 : M ∈ B.Lin
    · by_cases h2 : v ∈ M
      · by_cases h3 : InDual B 1 M
        · rw [if_pos h1, if_pos h2, if_pos h3, if_pos ⟨h1, h2, hD.1 h3⟩]; ring
        · rw [if_pos h1, if_pos h2, if_neg h3, if_neg (fun h => h3 (hD.2 h.2.2))]; ring
      · rw [if_pos h1, if_neg h2, zero_mul, mul_zero]
        exact (if_neg (fun h => h2 h.2.1)).symm
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  have hexp : HH B π I (S \ I) u 1 = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) := by
    have h1 : ∀ M, B.sgnLat M * term B π I (S \ I) u 1 M = ∑ p ∈ I.powerset ×ˢ (S \ I).powerset,
        (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
          (B.sgnLat M * term B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) M) := by
      intro M
      rw [Finset.sum_product, term, dlt, dlt, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [hterm0]; ring
    unfold HH
    simp_rw [h1]
    rw [finsum_mem_finset_sum_comm]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [mul_finsum_mem]
    · intro p hp
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
      refine (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF ∅ ∅ (Finset.empty_subset _) (Finset.empty_subset _) _ _
        ((hPlus p.1 (hp.1.trans hI)).1.mul hu) ((hPlus p.2 (hp.2.trans Finset.sdiff_subset)).1.mul isUnit_one)).subset ?_
      rintro M ⟨hM, hne⟩
      refine ⟨hM, fun h => hne ?_⟩
      simp only [h, mul_zero]
  rw [hexp]
  have hstep : ∀ p ∈ I.powerset ×ˢ (S \ I).powerset,
      (-1 : ℚ) ^ p.1.card * (-1 : ℚ) ^ p.2.card *
        HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
      (-1 : ℚ) ^ ((p.1 ∪ p.2) ∩ I).card * B.GG ((∏ j ∈ p.1 ∪ p.2, π j) * u) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have hdisj : Disjoint p.1 p.2 := Finset.disjoint_left.2 fun x h1 h2 =>
      (Finset.mem_sdiff.1 (hp.2 h2)).2 (hp.1 h1)
    have hcap : (p.1 ∪ p.2) ∩ I = p.1 := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (Finset.mem_sdiff.1 (hp.2 h)).2
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    have hy := hPlus p.2 (hp.2.trans Finset.sdiff_subset)
    have hm := GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit K B ι π ∅ ∅ ((∏ j ∈ p.1, π j) * u) 1 (∏ j ∈ p.2, π j) hL hy
    have hsq := eta_sq (K := K) (Algebra.norm K.E (∏ j ∈ p.2, π j))
    have hm' : HH B π ∅ ∅ ((∏ j ∈ p.1, π j) * u) ((∏ j ∈ p.2, π j) * 1) =
        K.eta (Algebra.norm K.E (∏ j ∈ p.2, π j)) *
          HH B π ∅ ∅ ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)) 1 := by
      rw [hm, ← mul_assoc, hsq, one_mul]
    rw [hm', heta p.2 (hp.2.trans Finset.sdiff_subset), hHG, hcap, Finset.prod_union hdisj]
    have h11 : ((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card) = 1 := by rw [← mul_pow]; norm_num
    calc (-1 : ℚ) ^ p.1.card * (-1) ^ p.2.card *
          ((-1) ^ p.2.card * B.GG ((∏ j ∈ p.2, π j) * ((∏ j ∈ p.1, π j) * u)))
        = (-1 : ℚ) ^ p.1.card * B.GG ((∏ j ∈ p.1, π j) * (∏ j ∈ p.2, π j) * u) *
          (((-1 : ℚ) ^ p.2.card) * ((-1 : ℚ) ^ p.2.card)) := by ring_nf
      _ = _ := by rw [h11, mul_one]
  rw [Finset.sum_congr rfl hstep]
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun J => (J ∩ I, J \ I)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    rw [Finset.mem_powerset]
    exact Finset.union_subset (hp.1.trans hI) (hp.2.trans Finset.sdiff_subset)
  · intro J hJ
    rw [Finset.mem_powerset] at hJ
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hJ le_rfl⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have h2 : ∀ x ∈ p.2, x ∉ I := fun x hx => (Finset.mem_sdiff.1 (hp.2 hx)).2
    refine Prod.ext ?_ ?_
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact h
        · exact absurd hx (h2 x h)
      · intro h; exact ⟨Or.inl h, hp.1 h⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hx⟩
        · exact absurd (hp.1 h) hx
        · exact h
      · intro h; exact ⟨Or.inr h, h2 x h⟩
  · intro J _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · intro p _
    rfl

end GlobalTheory.UnitLemma.Desc
