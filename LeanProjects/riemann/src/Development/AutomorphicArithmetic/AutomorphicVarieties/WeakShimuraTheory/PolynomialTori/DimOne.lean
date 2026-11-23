import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pow_le_of_primes {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (I : Ideal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = maximalIdeal B) : ∃ n, maximalIdeal B ^ n ≤ I := by
  have hle : maximalIdeal B ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQ⟩
    rw [h Q hQ hIQ]
  exact Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)

theorem UpperTheory.V.Ws.Po.dimOne :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B], ¬ Module.Finite O B →
      ∃ (P : Ideal B) (t : B) (n : ℕ), P.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ P ∧ t ∈ maximalIdeal B ∧ t ∉ P ∧
        maximalIdeal B ^ n ≤ P ⊔ Ideal.span {t} := by
  intro O _ _ _ B _ _ _ hnf
  haveI : IsLocalHom (algebraMap O B) := IsCO.isLocalHom
  have hIm : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O B) x hx
  have hex : ∃ Q : Ideal B, Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧
      Q ≠ maximalIdeal B := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := pow_le_of_primes _ (fun Q hQ hIQ => hcon Q hQ hIQ)
    exact hnf (UpperTheory.V.Ws.Po.finPow hIm IsCO.res_surj n hn)
  obtain ⟨P, ⟨hP, hIP, hPm⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian B B)
      {Q : Ideal B | Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧ Q ≠ maximalIdeal B} hex
  have hPle : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top
  obtain ⟨t, htm, htP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPle hPm)
  obtain ⟨n, hn⟩ := pow_le_of_primes (P ⊔ Ideal.span {t}) (by
    intro Q hQ hPQ
    by_contra hQm
    have hPQ' : P ≤ Q := le_trans le_sup_left hPQ
    have htQ : t ∈ Q := hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
    exact hmax Q ⟨hQ, hIP.trans hPQ', hQm⟩
      (lt_of_le_of_ne hPQ' (fun e => htP (by rw [e]; exact htQ))))
  exact ⟨P, t, n, hP, hIP, htm, htP, hn⟩
