import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace GlobalTheory.BdDim

theorem intRelation_coeff_eq_zero {A K L ι : Type} [CommRing A] [Field K] [Field L] (φ : A →+* K) (ψ : A →+* L)
    (hker : ∀ a, φ a = 0 → ψ a = 0) (y : ι → A)
    (ht : ∀ Q : MvPolynomial ι ℤ, aeval (fun i => ψ (y i)) Q = 0 → ∀ m, ((Q.coeff m : ℤ) : L) = 0)
    (n : ℕ) : ∀ P : MvPolynomial ι ℤ, aeval (fun i => φ (y i)) P = 0 → ∀ m, (P.coeff m).natAbs ≤ n →
      ((P.coeff m : ℤ) : K) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP m hn
    by_cases hm : P.coeff m = 0
    · simp [hm]
    have h1 : aeval (fun i => ψ (y i)) P = 0 := by
      have e1 := comp_aeval_apply (f := y) φ.toIntAlgHom P
      have e2 := comp_aeval_apply (f := y) ψ.toIntAlgHom P
      exact e2.symm.trans (hker _ (e1.trans hP))
    have hd : ∀ i, ((ringChar L : ℕ) : ℤ) ∣ P.coeff i := fun i =>
      (CharP.intCast_eq_zero_iff L (ringChar L) _).1 (ht P h1 i)
    obtain ⟨P', rfl⟩ := (C_dvd_iff_dvd_coeff _ _).2 hd
    rw [coeff_C_mul] at hm hn ⊢
    rw [map_mul, aeval_C] at hP
    rcases mul_eq_zero.1 hP with h | h
    · rw [Int.cast_mul, show (((ringChar L : ℕ) : ℤ) : K) = 0 from h, zero_mul]
    · have h0 : ringChar L ≠ 0 := fun h0 => hm (by simp [h0])
      have h1 : ringChar L ≠ 1 := CharP.ringChar_ne_one
      have h2 : 0 < (P'.coeff m).natAbs := Int.natAbs_pos.2 (right_ne_zero_of_mul hm)
      rw [Int.natAbs_mul, Int.natAbs_natCast] at hn
      have h3 : 2 ≤ ringChar L := by omega
      rw [Int.cast_mul, ih _ (by nlinarith) P' h m le_rfl, mul_zero]

theorem trdeg_bot_subring_eq (K : Type) [Field K] :
    Algebra.trdeg (⊥ : Subring K) K = Algebra.trdeg (⊥ : Subfield K) K := by
  let i : (⊥ : Subring K) →+* (⊥ : Subfield K) :=
    Subring.inclusion (show (⊥ : Subring K) ≤ (⊥ : Subfield K).toSubring from bot_le)
  letI := i.toAlgebra
  haveI : IsScalarTower (⊥ : Subring K) (⊥ : Subfield K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hi : Function.Injective i := fun a b h => Subtype.ext (congrArg (fun z : (⊥ : Subfield K) => (z : K)) h)
  haveI : FaithfulSMul (⊥ : Subring K) (⊥ : Subfield K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  haveI : Algebra.IsAlgebraic (⊥ : Subring K) (⊥ : Subfield K) := ⟨fun x => by
    rw [← isAlgebraic_algebraMap_iff (A := K) Subtype.val_injective]
    have hx : (x : K) ∈ Subfield.closure (∅ : Set K) := by simpa using x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 hx
    rw [Subring.closure_empty] at ha hb
    change IsAlgebraic _ (x : K)
    rw [← hab, div_eq_mul_inv]
    exact (isAlgebraic_algebraMap (⟨a, ha⟩ : (⊥ : Subring K))).mul
      (isAlgebraic_algebraMap (⟨b, hb⟩ : (⊥ : Subring K))).inv⟩
  rw [← trdeg_add_eq (⊥ : Subring K) (⊥ : Subfield K) (A := K),
    trdeg_eq_zero (R := (⊥ : Subring K)) (A := (⊥ : Subfield K)), zero_add]

theorem TrLe.of_ker_le {A K L : Type} [CommRing A] [Field K] [Field L] (φ : A →+* K) (ψ : A →+* L)
    (hψ : Function.Surjective ψ) (hker : ∀ a, φ a = 0 → ψ a = 0) {n : ℕ} (h : TrLe K n) : TrLe L n := by
  refine le_trans ?_ h
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (⊥ : Subfield L) L
  rw [← hs.cardinalMk_eq_trdeg, ← trdeg_bot_subring_eq]
  choose y hy using fun i : s => hψ i
  have ht : ∀ Q : MvPolynomial s ℤ, aeval (fun i => ψ (y i)) Q = 0 → ∀ m, ((Q.coeff m : ℤ) : L) = 0 := by
    intro Q hQ m
    have h1 : MvPolynomial.map (algebraMap ℤ (⊥ : Subfield L)) Q = 0 := by
      apply hs.1
      rw [map_zero, aeval_map_algebraMap, ← hQ]
      simp only [hy]
    have h2 := congrArg (fun R => ((coeff m R : (⊥ : Subfield L)) : L)) h1
    simpa [coeff_map] using h2
  refine AlgebraicIndependent.cardinalMk_le_trdeg (x := fun i => φ (y i)) ?_
  rw [algebraicIndependent_iff]
  intro Q hQ
  have hsurj : Function.Surjective (algebraMap ℤ (⊥ : Subring K)) := fun z => by
    obtain ⟨k, hk⟩ := Subring.mem_bot.1 z.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨P, rfl⟩ := map_surjective _ hsurj Q
  rw [aeval_map_algebraMap] at hQ
  ext m
  simpa [coeff_map] using intRelation_coeff_eq_zero φ ψ hker y ht _ P hQ m le_rfl

theorem trLe_residueField_of_specializes :
    ∀ (X : Scheme.{0}) (x y : X) (n : ℕ), x ⤳ y → TrLe (X.residueField x) n → TrLe (X.residueField y) n := by
  intro X x y n hxy h
  refine h.of_ker_le (X.presheaf.stalkSpecializes hxy ≫ X.residue x).hom (X.residue y).hom
    (X.residue_surjective y) fun a ha => ?_
  by_contra hne
  have hu : IsUnit a := by
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff a).2 hnu)
  exact (hu.map _).ne_zero ha

end GlobalTheory.BdDim

end
