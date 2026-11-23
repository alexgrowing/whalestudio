import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Cardinal

noncomputable section

theorem exists_ringHom_complex_ker_eq_of_isPrime {σ : Type} [Finite σ] (P : Ideal (MvPolynomial σ ℚ))
    [P.IsPrime] : ∃ φ : MvPolynomial σ ℚ →+* ℂ, ∀ f, φ f = 0 ↔ f ∈ P := by
  let Q := MvPolynomial σ ℚ ⧸ P
  let F := FractionRing Q
  have : CharZero F := charZero_of_injective_algebraMap (R := ℚ) (algebraMap ℚ F).injective
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  refine ⟨(ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P), fun f => ?_⟩
  have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
    ψ.injective.comp (IsFractionRing.injective Q F)
  rw [RingHom.comp_apply, map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]

theorem PullConeNull.proof : PullConeNull.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL
  set I := coneNullIdeal y L

  have hrad : ∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ∈ I.radical := by
    intro c
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) ⟨hIP, hP⟩
    obtain ⟨φ, hker⟩ := exists_ringHom_complex_ker_eq_of_isPrime P
    let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
    have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ (map (Int.castRingHom ℚ) f) := by
      intro f
      have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ.comp (map (Int.castRingHom ℚ)) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · exact RingHom.congr_fun (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C)
            ((φ.comp (map (Int.castRingHom ℚ))).comp C)) r
        · simp [z]
      exact RingHom.congr_fun h f
    by_contra hc
    have hz : z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_⟩
      · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
        exact Ideal.mul_mem_right _ P ((hker _).mp h0)
      · rw [hev, hker]
        exact hIP (Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩))
    obtain ⟨j, hj⟩ := hL z hz
    apply hj
    rw [hev, hker]
    exact hIP (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
  choose n hn using fun c => Ideal.mem_radical_iff.mp (hrad c)
  refine ⟨Finset.univ.sup n, fun c => ?_⟩
  have hle : n c ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ c)
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact I.mul_mem_right _ (hn c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
