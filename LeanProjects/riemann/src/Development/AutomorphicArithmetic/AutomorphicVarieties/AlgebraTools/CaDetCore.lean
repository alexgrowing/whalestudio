import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetLocus

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.under_le_of_det_mem :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A] [FaithfulSMul B A]
      (π : P →+* A), Function.Surjective π → relIdeal z m ≤ RingHom.ker π →
      ∀ Z : Ideal B, Z.IsPrime → ringKrullDim P ≤ ringKrullDim (B ⧸ Z) + (Fintype.card ι : ℕ) →
      (∀ Z' : Ideal A, Z'.IsPrime → Z'.comap (algebraMap B A) = Z → ∃ j, π (m j) ∉ Z') →
      ∀ Q' : Ideal A, Q'.IsPrime → π z.det ∈ Q' → Z ≤ Q'.comap (algebraMap B A) := by
  intro P _ _ ι _ _ z m hC B A _ _ _ _ _ π hπ hrel Z hZ hdim hm Q' hQ' hdet
  haveI := hZ
  have hinj : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  obtain ⟨Z', -, hZ'p, hZ'c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Z (⊥ : Ideal A) (by
    rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hZ'p
  haveI := hQ'
  obtain ⟨j, hj⟩ := hm Z' hZ'p hZ'c
  have hker : RingHom.ker ((Ideal.Quotient.mk Z').comp π) = Z'.comap π := by
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have e : P ⧸ Z'.comap π ≃+* A ⧸ Z' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp hπ))
  have hdimZ : ringKrullDim (P ⧸ Z'.comap π) = ringKrullDim (B ⧸ Z) := by
    rw [ringKrullDim_eq_of_ringEquiv e,
      ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := B) (B := A) Z', hZ'c]
  have hrelQ : ∀ I : Ideal A, relIdeal z m ≤ I.comap π := fun I x hx => by
    have h0 : π x = 0 := RingHom.mem_ker.mp (hrel hx)
    simp [Ideal.mem_comap, h0]
  have key := le_of_detIdeal_le P ι z m hC (Z'.comap π) inferInstance (hrelQ Z') ⟨j, hj⟩
    (by rw [hdimZ]; exact hdim) (Q'.comap π) inferInstance (by
      show relIdeal z m ⊔ Ideal.span {z.det} ≤ _
      refine sup_le (hrelQ Q') ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hdet)
  have hle : Z' ≤ Q' := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    exact key ha
  rw [← hZ'c]
  exact Ideal.comap_mono hle
