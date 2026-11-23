import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem ringKrullDim_quotient_le_comap_add_one {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {J : Type} {R : Type*} [CommRing R] [IsNoetherianRing R]
    (G' : Ideal (MRing (extIdx ι J) R)) [G'.IsPrime] (j₀ : J)
    (hY : ∀ j, j ≠ j₀ → (newVar j : MRing (extIdx ι J) R) ∈ G') :
    ringKrullDim (MRing (extIdx ι J) R ⧸ G') ≤
      ringKrullDim (MRing ι R ⧸ G'.comap (liftForm (J := J) (ι := ι) (R := R))) + 1 := by
  set G := G'.comap (liftForm (J := J) (ι := ι) (R := R)) with hGdef
  let φ : (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Ideal.quotientMap G' (liftForm (J := J) (ι := ι) (R := R)).toRingHom le_rfl
  let ψ : Polynomial (MRing ι R ⧸ G) →+* (MRing (extIdx ι J) R ⧸ G') :=
    Polynomial.eval₂RingHom φ (Ideal.Quotient.mk G' (newVar j₀))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine ⟨Polynomial.C (Ideal.Quotient.mk G (C a)), ?_⟩
      simp [ψ, φ, Ideal.quotientMap_mk, liftForm]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p v hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨o, i⟩ := v
      cases o with
      | none =>
        by_cases hi : i = j₀
        · subst hi
          refine ⟨a * Polynomial.X, ?_⟩
          rw [map_mul, ha, map_mul]
          congr 1
          simp [ψ, newVar]
        · refine ⟨0, ?_⟩
          rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
          exact G'.mul_mem_left _ (hY i hi)
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk G (X ⟨k, i⟩)), ?_⟩
        rw [map_mul, ha, map_mul]
        congr 1
        simp [ψ, φ, Ideal.quotientMap_mk, liftForm, rename_X]
  calc ringKrullDim (MRing (extIdx ι J) R ⧸ G')
      ≤ ringKrullDim (Polynomial (MRing ι R ⧸ G)) := ringKrullDim_le_of_surjective ψ hψ
    _ = ringKrullDim (MRing ι R ⧸ G) + 1 := Polynomial.ringKrullDim_of_isNoetherianRing

theorem mem_minimalPrimes_of_ringKrullDim {A : Type*} [CommRing A] (P G : Ideal A) [P.IsPrime]
    [G.IsPrime] (s : A) (hsP : s ∉ P) (N : ℕ) (hP : ringKrullDim (A ⧸ P) = (N : WithBot ℕ∞))
    (hle : P ⊔ Ideal.span {s} ≤ G) (hG : (N : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ G) + 1) :
    G ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
  refine ⟨⟨inferInstance, hle⟩, fun Q hQ hQG => ?_⟩
  have : Q.IsPrime := hQ.1
  by_contra hGQ
  have hsQ : s ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h => hsP (h ▸ hsQ)
  have h1 := DimStrictDrop.proof A Q G (lt_of_le_not_ge hQG hGQ)
  have h2 := DimStrictDrop.proof A P Q hPQ
  have h3 : (N : WithBot ℕ∞) + 1 ≤ (N : WithBot ℕ∞) :=
    calc (N : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ G) + 1 + 1 := by gcongr
      _ ≤ ringKrullDim (A ⧸ Q) + 1 := by gcongr
      _ ≤ N := hP ▸ h2
  have h4 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : N + 1 ≤ N := by exact_mod_cast h4
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
