import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
open IsLocalRing TensorProduct

noncomputable section

namespace GlobalTheory

def intDerivationOfLeibniz {A M : Type} [CommRing A] [AddCommGroup M] {instZA : Algebra ℤ A}
    {_ : Module A M} {instZM : Module ℤ M} (f : A →+ M) (h : ∀ a b, f (a * b) = a • f b + b • f a) :
    Derivation ℤ A M :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      obtain rfl : instZM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
      obtain rfl : instZA = Ring.toIntAlgebra A := Subsingleton.elim _ _
      exact map_zsmul f c x
    map_one_eq_zero' := by
      have h1 := h 1 1
      rw [one_mul, one_smul] at h1
      simpa using h1
    leibniz' := h }

theorem derivation_extend_completion_localization_atPrime (S : Type) [CommRing S] (P : Ideal S)
    [P.IsPrime] (d : Derivation ℤ S S) :
    ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
      (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)),
      ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ S (Localization.AtPrime P) P
    (intDerivationOfLeibniz
      ((algebraMap S (Localization.AtPrime P)).toAddMonoidHom.comp d.toLinearMap.toAddMonoidHom)
      (fun a b => by simp [d.leibniz, Algebra.smul_def]))
  have hadd : ∀ y z, BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D' (y + z) =
      BK.complDerFun _ D' y + BK.complDerFun _ D' z := fun y z => by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) y)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) z)
    rw [BK.evalₐ_complDerFun _ D' (r := r + t) (by rw [map_add, map_add, hr, ht]), map_add,
      map_add, map_add, BK.evalₐ_complDerFun _ D' hr.symm, BK.evalₐ_complDerFun _ D' ht.symm]
  refine ⟨intDerivationOfLeibniz
    { toFun := BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D'
      map_zero' := by
        have h0 := hadd 0 0
        rw [add_zero] at h0
        simpa using h0
      map_add' := hadd }
    (fun a b => by simpa [smul_eq_mul] using BK.complDerFun_mul _ D' a b),
    fun x => ?_⟩
  have h2 := BK.complDerFun_algebraMap (maximalIdeal (Localization.AtPrime P)) D'
    (algebraMap S (Localization.AtPrime P) x)
  rw [hD'] at h2
  exact h2

end GlobalTheory
