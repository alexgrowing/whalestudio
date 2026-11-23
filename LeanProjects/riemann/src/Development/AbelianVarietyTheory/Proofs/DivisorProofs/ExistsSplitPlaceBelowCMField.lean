import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceExists

theorem exists_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, hsplit⟩ := GlobalTheory.SplitRealPrime.exists_prime_isSplitAt E

  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (by rw [hx, map_zero])
      rw [this]
      exact Ideal.zero_mem _)
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : ((p : ℤ)) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hQ]
      exact Ideal.subset_span rfl
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hQ0 : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
  exact ⟨⟨Q, hQmax.isPrime, hQ0⟩, hsplit _ hpQ⟩

end GlobalTheory.SplitPlaceExists
