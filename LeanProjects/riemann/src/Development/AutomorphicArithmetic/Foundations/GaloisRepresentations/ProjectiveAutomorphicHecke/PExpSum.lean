import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImagOfSq
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem imag_of_sq {c : ℂ} {d : ℕ} (hd : 0 < d) (h : c ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) c = -c ∧ c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qh67.imag_of_sq hd h

private theorem sum_emb {E : Type} [Field E] [NumberField E]
    (hc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ) (f : (E →+* ℂ) → ℤ) :
    ∑ φ, f φ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq φ with h | h
      · left; exact h.symm
      · right; rw [h]; exact (ComplexEmbedding.involutive_conjugate E φ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hfib, Finset.sum_pair (hc _).symm]

theorem UpperTheory.Gal.CertificateRingHomMap.pExpSum_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum := by
  intro E _ _ _ n d x hd hx W m hm τ
  have hsq : ∀ φ : E →+* ℂ, (φ x) ^ 2 = -(d : ℂ) := fun φ => by
    rw [← map_pow, hx]; simp
  have hτ0 : τ x ≠ 0 := (imag_of_sq hd (hsq τ)).2
  have hcj : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ x = -φ x := fun φ => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact (imag_of_sq hd (hsq φ)).1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ h => by
    have h1 := hcj φ
    rw [h] at h1
    have h2 : φ x ≠ 0 := (imag_of_sq hd (hsq φ)).2
    exact h2 (self_eq_neg.1 h1)
  have hpm : ∀ φ : E →+* ℂ, φ x = τ x ∨ φ x = -τ x := fun φ =>
    sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq φ).trans (hsq τ).symm)
  have hnn : τ x ≠ -τ x := fun h => hτ0 (self_eq_neg.1 h)
  have hl0 : ∀ v : InfinitePlace E, ∑ j, lamOf W m v.embedding j = n * m v := fun v => by
    simp [lamOf, InfinitePlace.mk_embedding]
  have hl1 : ∀ v : InfinitePlace E, ((∑ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j : ℕ) : ℤ) =
      ∑ i, (W v).w i + n * m v := fun v => by
    have hv : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
      rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    have h1 : ∀ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j = ((W v).w j + m v).toNat := fun j => by
      unfold lamOf
      rw [hv, if_neg (hne _)]
    simp only [h1]
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hm v i), Finset.sum_add_distrib]
    simp
  set F : (E →+* ℂ) → ℤ := fun φ => (((if φ x = -τ x then 1 else 0) * ∑ j, lamOf W m φ j : ℕ) : ℤ) with hF
  have hFv : ∀ v : InfinitePlace E, F v.embedding + F (ComplexEmbedding.conjugate v.embedding) =
      n * m v + if v.embedding x = -τ x then 0 else ∑ i, (W v).w i := fun v => by
    simp only [hF, hcj]
    rcases hpm v.embedding with h | h
    · have h1 : v.embedding x ≠ -τ x := by rw [h]; exact hnn
      have h2 : -v.embedding x = -τ x := by rw [h]
      rw [if_neg h1, if_pos h2, if_neg h1, zero_mul, one_mul, hl1]
      push_cast; ring
    · have h2 : -v.embedding x ≠ -τ x := by rw [h, neg_neg]; exact hnn
      rw [if_pos h, if_neg h2, if_pos h, zero_mul, one_mul, hl0]
      push_cast; ring
  have hF1 : ∑ φ, F φ = mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ := by
    rw [sum_emb hne, Finset.sum_congr rfl fun v _ => hFv v]
    unfold mOf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  have hmem : ComplexEmbedding.conjugate τ ∈ Finset.univ.erase τ :=
    Finset.mem_erase.2 ⟨hne τ, Finset.mem_univ _⟩
  have hF2 : ∑ φ, F φ = F τ + (F (ComplexEmbedding.conjugate τ) +
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), F φ) := by
    rw [Finset.add_sum_erase _ F hmem, Finset.add_sum_erase _ F (Finset.mem_univ τ)]
  have hFτ : F τ = 0 := by simp only [hF]; rw [if_neg hnn]; simp
  have hFc : F (ComplexEmbedding.conjugate τ) = n * m (InfinitePlace.mk τ) +
      if τ = (InfinitePlace.mk τ).embedding then ∑ i, (W (InfinitePlace.mk τ)).w i else 0 := by
    simp only [hF]
    rw [if_pos (hcj τ), one_mul]
    split_ifs with h
    · conv_lhs => rw [h]
      rw [hl1]
      ring
    · have h' : ComplexEmbedding.conjugate τ = (InfinitePlace.mk τ).embedding := by
        rcases InfinitePlace.embedding_mk_eq τ with h1 | h1
        · exact absurd h1.symm h
        · exact h1.symm
      rw [h', hl0]
      push_cast; ring
  rw [← hF1, hF2, hFτ, hFc, zero_add]
  simp only [hF]
  push_cast
  ring
