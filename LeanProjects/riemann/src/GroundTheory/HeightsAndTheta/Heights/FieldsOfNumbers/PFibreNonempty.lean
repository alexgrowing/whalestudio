import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreNonempty
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem FibreNonempty.proof (h1 : SemilocalFiniteRank.Statement.{u})
    (h2 : DegZeroLocalRing.Statement.{u}) : FibreNonempty.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hn hc W hW hWn hle
  have := hP'.isPrime
  by_contra hem
  rw [Set.not_nonempty_iff_eq_empty] at hem
  obtain ⟨hfin, -, -⟩ := h1 F K K' j ι' P' hP' n hn hc W hW hWn hle
  have := hfin
  have hnone : ∀ W' ∈ fibrePrimes j P' W, False := fun W' hW' => by
    rw [hem] at hW'
    exact hW'

  have hB : IsField (degZeroLoc P' (fibrePrimes j P' W)) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro x hx
    obtain ⟨b, f, g, hf, hg, hgP, -, hxfg⟩ := DegZeroLocQuot.proof F K' ι' P' (fibrePrimes j P' W)
      (fun W' hW' => (hnone W' hW').elim) x.1 x.2
    have hfP : f ∉ P' := by
      intro hfP
      apply hx
      apply Subtype.ext
      rw [hxfg, Ideal.Quotient.eq_zero_iff_mem.mpr hfP, map_zero, zero_div]
      rfl
    refine ⟨⟨_, div_mem_degZeroLoc P' (fibrePrimes j P' W) hg hf hfP
      (fun W' hW' => (hnone W' hW').elim)⟩, ?_⟩
    have hne : ∀ a : MRing ι' F, a ∉ P' →
        algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' a) ≠ 0 :=
      fun a ha => by
        rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
    apply Subtype.ext
    change x.1 * _ = 1
    rw [hxfg, div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P' f))]
    exact div_self (mul_ne_zero (hne g hgP) (hne f hfP))

  have hinj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro x y hxy
    have := congrArg (fun z : degZeroLoc P' (fibrePrimes j P' W) =>
      (z : FractionRing (MRing ι' F ⧸ P'))) hxy
    simp only [degZeroLoc.algebraMap_contract_coe] at this
    exact Subtype.ext ((contractFracMap j P').toRingHom.injective this)
  have : Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) := Algebra.IsIntegral.of_finite _ _
  have hA := isField_of_isIntegral_of_isField hinj hB
  have hdim := (h2 F K (fun k => ι' (j k)) (contractPrime j P')
    (isMultiProjPrime_contractPrime j ι' hP') W hW hle).2 n hc hWn
  rw [ringKrullDim_eq_zero_of_isField hA] at hdim
  exact zero_ne_one hdim

end

end GroundTheory.Heights₂.Heights.FieldNumbers
