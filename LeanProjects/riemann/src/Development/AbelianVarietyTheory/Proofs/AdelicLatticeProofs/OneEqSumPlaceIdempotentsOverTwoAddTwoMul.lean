import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

theorem evalV_singleV_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_singleV_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem half_mem_adicCompletionIntegers (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (h : (2 : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  rw [h2, map_inv₀, h1, inv_one]

theorem one_eq_sum_singleV_add_two_mul : ∀ (F : Type) [Field F] [NumberField F], ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (2 : 𝓞 F) ∈ v.asIdeal) ∧ (∀ v : HeightOneSpectrum (𝓞 F), singleV F v 1 ∈ intAf F ∧ evalV F v (singleV F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV F v' (singleV F v 1) = 0) ∧ ∃ β ∈ intAf F, (1 : Af F) = ∑ v ∈ P, singleV F v 1 + 2 * β := by
  intro F _ _
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv, fun v => ⟨fun w => ?_, evalV_singleV_same F v,
    evalV_singleV_ne F v⟩, algebraMap F (Af F) (2 : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1),
    fun w => ?_, ?_⟩
  · by_cases hw : w = v
    · subst hw
      rw [evalV_singleV_same]; exact one_mem _
    · rw [evalV_singleV_ne F v w hw]; exact zero_mem _
  · rw [map_mul, map_sub, map_one, map_sum, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_singleV_ne F b w hb.symm,
        evalV_singleV_same, sub_self, mul_zero]
      exact zero_mem _
    · rw [Finset.sum_eq_zero fun b hb => evalV_singleV_ne F b w fun h => hw (h ▸ hb), sub_zero, mul_one]
      exact half_mem_adicCompletionIntegers F w (by simpa using hw)
  · have h2 : (2 : Af F) * algebraMap F (Af F) (2 : F)⁻¹ = 1 := by
      rw [← map_ofNat (algebraMap F (Af F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    rw [← mul_assoc, h2, one_mul, add_sub_cancel]

end GlobalTheory.LatVac
