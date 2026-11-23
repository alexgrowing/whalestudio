import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DenInt

open IsDedekindDomain

theorem intRing_of_isIntegral {F : Type} [Field F] [NumberField F] {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Af F) c ∈ GlobalTheory.HolDict.ShortVec.intRing F := by
  refine GlobalTheory.HolDict.ShortVec.mem_intRing.2 fun v => ?_
  rw [AlgHom.commutes]
  refine Valued.toNormedField.norm_le_one_iff.2 ?_
  have := HeightOneSpectrum.valuation_le_one (K := F) v (⟨c, hc⟩ : 𝓞 F)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c).trans_le this

theorem exists_den (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  set b := Module.finBasis D.host.F D.host.E
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E
  obtain ⟨b', hb⟩ : ∃ b' : Fin (Module.finrank D.host.F D.host.E) → D.host.E,
      ∀ x k, Algebra.trace D.host.F D.host.E (b' k * x) = b.repr x k :=
    ⟨fun k => ((Algebra.traceForm D.host.F D.host.E).toDual (traceForm_nondegenerate D.host.F D.host.E)).symm (b.coord k),
      fun x k => LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate D.host.F D.host.E) (b.coord k) x⟩
  obtain ⟨d, hd, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (integralClosure ℤ D.host.E).toSubring b' fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b' k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨d, hd, fun x hx k => ?_⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k = algebraMap D.host.F (Af D.host.F) (b.repr x k) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.algebraMap_eq_smul_one]
  have e2 : (d : D.host.F) * b.repr x k = Algebra.trace D.host.F D.host.E (((d : D.host.E) * b' k) * x) := by
    rw [← hb, mul_assoc, ← nsmul_eq_mul d (b' k * x), map_nsmul, nsmul_eq_mul]
  have hi : IsIntegral ℤ ((d : D.host.F) * b.repr x k) := by
    rw [e2]
    exact Algebra.isIntegral_trace ((h k).mul hx)
  rw [e1, ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul]
  exact intRing_of_isIntegral hi

end GlobalTheory.DenInt
