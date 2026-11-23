import Mathlib

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal MvPolynomial

noncomputable section

theorem trdeg_lt_of_surjective_of_ker_ne_bot {R B C : Type} [CommRing R] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≠ ⊥)
    (hinj : Function.Injective (algebraMap R C)) (hfin : trdeg R B < ℵ₀) :
    trdeg R C < trdeg R B := by
  have : Nontrivial R := (algebraMap R C).domain_nontrivial
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hinj
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R C
  have hCle : trdeg R C ≤ trdeg R B := trdeg_le_of_surjective f hf
  have hs_card : #s = trdeg R C := hs.cardinalMk_eq_trdeg
  have : Finite s := Cardinal.lt_aleph0_iff_finite.mp (hs_card ▸ hCle.trans_lt hfin)
  let y : s → B := fun i => Function.surjInv hf (i : C)
  have hfy : ∀ i, f (y i) = i := fun i => Function.surjInv_eq hf _
  have hfy' : (fun i => f (y i)) = ((↑) : s → C) := funext hfy
  have hy : AlgebraicIndependent R y := AlgebraicIndependent.of_comp f (by
    change AlgebraicIndependent R (fun i => f (y i))
    rw [hfy']
    exact hs.1)
  by_contra hlt
  push Not at hlt
  have hyb : IsTranscendenceBasis R y :=
    hy.isTranscendenceBasis_of_trdeg_le_of_finite (hlt.trans hs_card.ge)
  have halg := hyb.isAlgebraic
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hq0 hq (halg.isAlgebraic q)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have ha' : f (a : B) = 0 := by
    simpa [Ideal.mem_comap, RingHom.mem_ker] using ha
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial s R, aeval y P = a := by
    have h : (a : B) ∈ (aeval y : MvPolynomial s R →ₐ[R] B).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact a.2
    exact h
  have hPx : aeval ((↑) : s → C) P = 0 := by
    rw [← hfy', ← comp_aeval_apply, hP, ha']
  have hP0 : P = 0 := hs.1 (hPx.trans (map_zero _).symm)
  apply ha0
  apply Subtype.ext
  rw [← hP, hP0, map_zero]
  rfl

theorem trdeg_zmod_quotient_le {B : Type} [CommRing B] [IsDomain B] [Algebra ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (p : ℕ) [Fact p.Prime] (Q : Ideal B) [Q.IsPrime]
    [CharP (B ⧸ Q) p] :
    letI := ZMod.algebra (B ⧸ Q) p
    trdeg (ZMod p) (B ⧸ Q) ≤ trdeg ℤ B := by
  let := ZMod.algebra (B ⧸ Q) p
  have : FaithfulSMul (ZMod p) (B ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (ZMod p) (B ⧸ Q)).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (B ⧸ Q)
  rw [← hs.cardinalMk_eq_trdeg]
  let y : s → B := fun i => Function.surjInv Ideal.Quotient.mk_surjective (i : B ⧸ Q)
  have hy : (fun i => Ideal.Quotient.mkₐ ℤ Q (y i)) = ((↑) : s → B ⧸ Q) :=
    funext fun i => Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hp0 : (p : B) ≠ 0 := by
    intro h
    have : algebraMap ℤ B (p : ℤ) = algebraMap ℤ B 0 := by simpa using h
    exact (Nat.Prime.ne_zero (Fact.out : p.Prime)) (by exact_mod_cast hinj this)

  have hred : ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      MvPolynomial.map (algebraMap ℤ (ZMod p)) P = 0 := by
    intro P hP
    apply hs.1
    have hc : (algebraMap (ZMod p) (B ⧸ Q)).comp (algebraMap ℤ (ZMod p)) = algebraMap ℤ (B ⧸ Q) :=
      RingHom.ext_int _ _
    rw [map_zero, aeval_def, eval₂_map, hc, ← aeval_def, ← hy, ← comp_aeval_apply, hP, map_zero]
  have key : ∀ n : ℕ, ∀ P : MvPolynomial s ℤ, aeval y P = 0 →
      ∀ m, P.coeff m ≠ 0 → (P.coeff m).natAbs ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hP m hm hn
      have hdvd : C (p : ℤ) ∣ P := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (MvPolynomial.coeff i) (hred P hP)
        rw [coeff_map, coeff_zero, algebraMap_int_eq, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact this
      obtain ⟨P', rfl⟩ := hdvd
      have hP' : aeval y P' = 0 := by
        rw [map_mul, aeval_C] at hP
        rcases mul_eq_zero.mp hP with h | h
        · exact absurd (by simpa using h) hp0
        · exact h
      rw [coeff_C_mul] at hm hn
      have hm' : P'.coeff m ≠ 0 := right_ne_zero_of_mul hm
      have hlt : (P'.coeff m).natAbs < n := by
        rw [Int.natAbs_mul] at hn
        have h2 : 2 ≤ ((p : ℤ)).natAbs := by
          simpa using (Fact.out : p.Prime).two_le
        have h1 : 0 < (P'.coeff m).natAbs := Int.natAbs_pos.mpr hm'
        nlinarith
      exact ih _ hlt P' hP' m hm' le_rfl
  refine AlgebraicIndependent.cardinalMk_le_trdeg (R := ℤ) (x := y) ?_
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  exact key _ P hP m hm le_rfl

end

end GroundTheory.Heights₂.Heights
