import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem exists_extend_residue {O A F : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Algebra.IsIntegral O A] (hinj : Function.Injective (algebraMap O A)) [Field F] [IsAlgClosed F]
    (κ : IsLocalRing.ResidueField O →+* F) :
    ∃ g : A →+* F, g.comp (algebraMap O A) = κ.comp (IsLocalRing.residue O) := by
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (IsLocalRing.maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (A ⧸ Q) := Ideal.Quotient.field Q
  let j : IsLocalRing.ResidueField O →+* A ⧸ Q := Ideal.quotientMap Q (algebraMap O A) hQm.ge
  have hj : j.comp (IsLocalRing.residue O) = (Ideal.Quotient.mk Q).comp (algebraMap O A) := by
    ext x; rfl
  letI : Algebra (IsLocalRing.ResidueField O) (A ⧸ Q) := j.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) F := κ.toAlgebra
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
    refine ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (j.comp (IsLocalRing.residue O)) _ _ = 0
    rw [hj, ← hom_eval₂, hpa, map_zero]⟩
  let L : (A ⧸ Q) →ₐ[IsLocalRing.ResidueField O] F := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  rw [RingHom.comp_assoc, ← hj, ← RingHom.comp_assoc]
  congr 1
  ext x
  exact L.commutes x

theorem exists_redVia : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
      InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  intro D i k _
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hφ : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  letI : Algebra (D.nd.O i) ℂ := (iotaO D.nd D.naut i).toAlgebra
  let A := integralClosure (D.nd.O i) ℂ
  have hA : Function.Injective (algebraMap (D.nd.O i) A) := fun x y h => hφ (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_extend_residue hA (D.naut.kFbar i)
  have hmem : ∀ x, D.ntypes.teichC k x ∈ A := by
    intro x
    by_cases hx : x = 0
    · rw [hx, GlobalTheory.TameLabels.teich_zero _ (D.ntypes.teichC_inj k)]; exact A.zero_mem
    · obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1
        ((D.ntypes.teichC k).isOfFinOrder (GlobalTheory.TameLabels.isOfFinOrder_of_ne_zero hx))
      exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  let t : Fb (D.host.g k) (D.host.g_prime k) →* A := (D.ntypes.teichC k).codRestrict A.toSubmonoid hmem
  have ht : ∀ x, (t x : ℂ) = D.ntypes.teichC k x := fun _ => rfl
  refine ⟨g.toMonoidHom.comp t, fun x y hx hy hcx hcy h => ?_, fun p s hp => ?_⟩
  · refine D.ntypes.teichC_inj k x y hx hy ?_
    rw [← ht, ← ht]
    congr 1
    refine GlobalTheory.TameRed.eq_of_map_eq g (M := orderOf x * orderOf y) ?_ ?_ ?_ h
    · rw [Ne, CharP.cast_eq_zero_iff _ (D.nd.l i)]
      exact (Nat.Prime.coprime_iff_not_dvd (D.nd.lPrime i).out).1 (Nat.Coprime.mul_left hcx hcy).symm
    · rw [← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
    · rw [← map_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
  · have h1 : p.map (algebraMap (D.nd.O i) A) = (s.map fun x => X - C (t x)).prod := by
      apply Polynomial.map_injective A.val.toRingHom Subtype.val_injective
      rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
      refine hp.trans (congrArg _ (Multiset.map_congr rfl fun x _ => ?_))
      simp [ht]
    rw [← hg, ← Polynomial.map_map, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
    simp

end GlobalTheory.TypeLeaf
