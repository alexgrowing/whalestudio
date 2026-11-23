import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem monic_of_mem_normalizedFactors {P q : k[X]} (hq : q ∈ normalizedFactors P) : q.Monic := by
  have h0 : q ≠ 0 := (irreducible_of_normalized_factor q hq).ne_zero
  rw [← normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize h0

theorem monic_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    (∏ q ∈ t, q).Monic := by
  exact Polynomial.monic_prod_of_monic t id fun q hq => monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 (ht hq))

theorem normalizedFactors_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    normalizedFactors (∏ q ∈ t, q) = t.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id',
    normalizedFactors_prod_eq _ fun q hq => irreducible_of_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))]
  conv_rhs => rw [← Multiset.map_id t.val]
  exact Multiset.map_congr rfl fun q hq => normalize_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))

theorem prod_sub_dvd {P : k[X]} (hP : P ≠ 0) (t : Finset k[X])
    (ht : t ⊆ (normalizedFactors P).toFinset) : (∏ q ∈ t, q) ∣ P := by
  have h0 : (∏ q ∈ t, q) ≠ 0 := (monic_prod_sub t ht).ne_zero
  rw [dvd_iff_normalizedFactors_le_normalizedFactors h0 hP, normalizedFactors_prod_sub t ht]
  exact (Multiset.le_iff_subset t.nodup).2 fun q hq => Multiset.mem_toFinset.1 (ht hq)

theorem eq_prod_sub {P Q : k[X]} (hP : P ≠ 0) (hsq : Squarefree P) (hQ : Q.Monic) (hQP : Q ∣ P) :
    (normalizedFactors Q).toFinset ⊆ (normalizedFactors P).toFinset ∧
      Q = ∏ q ∈ (normalizedFactors Q).toFinset, q := by
  have hQ0 := hQ.ne_zero
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hQ0 hP).1 hQP
  refine ⟨fun a ha => Multiset.mem_toFinset.2 (Multiset.mem_of_le hle (Multiset.mem_toFinset.1 ha)), ?_⟩
  have hnd : (normalizedFactors Q).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hQ0).1 (hsq.squarefree_of_dvd hQP)
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
    prod_normalizedFactors_eq hQ0]
  exact ((Polynomial.normalize_eq_self_iff_monic hQ0).2 hQ).symm

end GlobalTheory.DivSum

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem isCoprime_of_sub {P q : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset)
    (hq : q ∈ (normalizedFactors P).toFinset) (hqt : q ∉ t) : IsCoprime q (∏ r ∈ t, r) := by
  refine IsCoprime.prod_right fun r hr => ?_
  have hqP := Multiset.mem_toFinset.1 hq
  have hrP := Multiset.mem_toFinset.1 (ht hr)
  rw [(irreducible_of_normalized_factor q hqP).coprime_iff_not_dvd]
  intro hd
  exact hqt (normalizedFactors_eq_of_dvd P q hqP r hrP hd ▸ hr)

theorem s_prod_sub {P : k[X]} (hP : P ≠ 0) (s : k[X] → ℂ)
    (hmul : ∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂)
    (h1 : s 1 = 1) (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    s (∏ q ∈ t, q) = ∏ q ∈ t, s q := by
  induction t using Finset.induction_on with
  | empty => simp [h1]
  | insert a t ha ih =>
    have ht' : t ⊆ (normalizedFactors P).toFinset := fun x hx => ht (Finset.mem_insert_of_mem hx)
    have haP : a ∈ (normalizedFactors P).toFinset := ht (Finset.mem_insert_self a t)
    have hma : a.Monic := monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 haP)
    have hd : a * ∏ q ∈ t, q ∣ P := by
      have h := prod_sub_dvd hP _ ht
      rwa [Finset.prod_insert ha] at h
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hmul _ _ hma (monic_prod_sub t ht') hd (isCoprime_of_sub t ht' haP ha), ih ht']

theorem finsum_monic_divisors_sign : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ,
    (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) →
    (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) →
    {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧
      ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 =
        if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  intro k _ P hPm hPs s hmul hsgn
  have hP : P ≠ 0 := hPm.ne_zero
  have hsq : Squarefree P := hPs.squarefree
  set F := (normalizedFactors P).toFinset with hF
  have memF : ∀ q ∈ F, q.Monic ∧ q ∣ P := fun q hq =>
    ⟨monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq)⟩
  have h1 : s 1 = 1 := by
    have hm := hmul 1 1 monic_one monic_one (by rw [one_mul]; exact one_dvd P) isCoprime_one_left
    rw [one_mul] at hm
    rcases hsgn 1 monic_one (one_dvd P) with h | h
    · exact h
    · rw [h] at hm
      norm_num at hm
  let φ : {t // t ∈ F.powerset} → {Q : k[X] // Q.Monic ∧ Q ∣ P} := fun t =>
    ⟨∏ q ∈ t.1, q, monic_prod_sub t.1 (Finset.mem_powerset.1 t.2),
      prod_sub_dvd hP t.1 (Finset.mem_powerset.1 t.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg (fun Q : {Q : k[X] // Q.Monic ∧ Q ∣ P} => normalizedFactors Q.1) hab
    simp only [φ] at h
    rw [normalizedFactors_prod_sub a.1 (Finset.mem_powerset.1 a.2),
      normalizedFactors_prod_sub b.1 (Finset.mem_powerset.1 b.2)] at h
    exact Subtype.ext (Finset.val_injective h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨Q, hQm, hQd⟩
    obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
    exact ⟨⟨_, Finset.mem_powerset.2 hsub⟩, Subtype.ext heq.symm⟩
  have hs1 : ∀ q ∈ F, s q = 1 ∨ s q = -1 := fun q hq => hsgn q (memF q hq).1 (memF q hq).2
  refine ⟨?_, ?_⟩
  · have hsub : {Q : k[X] | Q.Monic ∧ Q ∣ P} ⊆ ((F.powerset.image fun t => ∏ q ∈ t, q : Finset k[X]) : Set k[X]) := by
      intro Q hQ
      obtain ⟨⟨t, ht⟩, htQ⟩ := hsurj ⟨Q, hQ⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, congrArg Subtype.val htQ⟩)
    exact (Finset.finite_toSet _).subset hsub
  · rw [← finsum_comp_equiv (Equiv.ofBijective φ ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
    have hsum : ∑ t : {t // t ∈ F.powerset}, s (Equiv.ofBijective φ ⟨hinj, hsurj⟩ t).1 = ∏ q ∈ F, (1 + s q) := by
      rw [Finset.prod_one_add, ← Finset.sum_coe_sort F.powerset]
      refine Finset.sum_congr rfl fun t _ => ?_
      exact s_prod_sub hP s hmul h1 t.1 (Finset.mem_powerset.1 t.2)
    rw [hsum]
    split_ifs with hall
    · rw [Finset.prod_congr rfl fun q hq => show 1 + s q = 2 by
        rw [hall q (memF q hq).1 (memF q hq).2]
        norm_num, Finset.prod_const]
      have hnd : (normalizedFactors P).Nodup := (squarefree_iff_nodup_normalizedFactors hP).1 hsq
      rw [hF, Multiset.card_toFinset, hnd.dedup]
      rfl
    · push_neg at hall
      obtain ⟨Q, hQm, hQd, hQs⟩ := hall
      obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
      have hsQ := s_prod_sub hP s hmul h1 _ hsub
      rw [← heq] at hsQ
      by_contra hne
      apply hQs
      rw [hsQ]
      refine Finset.prod_eq_one fun q hq => ?_
      rcases hs1 q (hsub hq) with h | h
      · exact h
      · exact absurd (Finset.prod_eq_zero (hsub hq) (by rw [h]; norm_num)) hne

end GlobalTheory.DivSum
