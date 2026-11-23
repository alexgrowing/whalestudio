import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT

theorem factorPow_evalₐ_adic {B : Type} [CommRing B] (J : Ideal B) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion J B) :
    Ideal.Quotient.factorPow J h (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J B x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have hs := s.prop h
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hs
  rw [← neg_sub]
  exact (J ^ m).neg_mem hs

theorem exists_adicCompletion_extension {B : Type} [CommRing B] (l : ℕ)
    (f : B →+* AdicCompletion (Ideal.span {(l : B)}) B) :
    ∃ g : AdicCompletion (Ideal.span {(l : B)}) B →+* AdicCompletion (Ideal.span {(l : B)}) B,
      ∀ b, g (algebraMap B _ b) = f b := by
  have hJ : ∀ n, ∀ b ∈ Ideal.span {(l : B)} ^ n,
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) = 0 := by
    intro n b hb
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]
    have hl : ((l : B ⧸ Ideal.span {(l : B)} ^ n)) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : B)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hl, zero_mul]
  let ψ : ∀ n, B ⧸ Ideal.span {(l : B)} ^ n →+* B ⧸ Ideal.span {(l : B)} ^ n := fun n =>
    Ideal.Quotient.lift (Ideal.span {(l : B)} ^ n)
      ((AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _).comp f) (hJ n)
  have hψ : ∀ n b, ψ n (Ideal.Quotient.mk _ b) =
      AdicCompletion.evalₐ (Ideal.span {(l : B)}) n (f b) := fun n b => rfl
  let F : ∀ n, AdicCompletion (Ideal.span {(l : B)}) B →+* B ⧸ Ideal.span {(l : B)} ^ n :=
    fun n => (ψ n).comp (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n : _ →+* _)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.span {(l : B)}) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(l : B)}) n x)
    simp only [F, RingHom.comp_apply, RingHom.coe_coe]
    rw [← factorPow_evalₐ_adic _ hle x, ← hb, hψ, factorPow_evalₐ_adic, Ideal.Quotient.factor_mk, hψ]
  refine ⟨AdicCompletion.liftRingHom _ F hF, fun b => ?_⟩
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_liftRingHom]
  simp only [F, RingHom.comp_apply, RingHom.coe_coe]
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, hψ]
  rfl

theorem exists_EE_extension {l : ℕ} {O : Type} [CommRing O] (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hu : IsUnit (algebraMap O⟦X⟧ (EE O l) (ψ X))) :
    ∃ ψE : EE O l →ₐ[O] EE O l,
      ∀ a, ψE (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
  have hu' : IsUnit (((algebraMap O⟦X⟧ (EE O l)).comp (ψ : O⟦X⟧ →+* O⟦X⟧)) X) := hu
  obtain ⟨g, hg⟩ := exists_adicCompletion_extension l
    (IsLocalization.Away.lift (X : O⟦X⟧) (S := Localization.Away (X : O⟦X⟧)) hu')
  have key : ∀ a, g (algebraMap O⟦X⟧ (EE O l) a) = algebraMap O⟦X⟧ (EE O l) (ψ a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (EE O l), hg,
      IsLocalization.Away.lift_eq]
    rfl
  refine ⟨{ g with commutes' := fun c => ?_ }, key⟩
  show g (algebraMap O (EE O l) c) = algebraMap O (EE O l) c
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧ (EE O l), key, AlgHom.commutes]

end GlobalTheory.NB.LT
