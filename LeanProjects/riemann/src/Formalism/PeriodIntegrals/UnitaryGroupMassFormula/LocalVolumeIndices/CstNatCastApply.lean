import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.CompPiVLocGSame

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst)

theorem Cst_inv_int (v : HeightOneSpectrum (𝓞 I.F)) (m : ℕ) (hm : (m : 𝓞 I.F) ∉ v.asIdeal) :
    ((m : Fv I.F v))⁻¹ ∈ v.adicCompletionIntegers I.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
  have e1 : (m : Fv I.F v) = ((algebraMap (𝓞 I.F) I.F (m : 𝓞 I.F) : I.F) : Fv I.F v) := by
    rw [← map_natCast (algebraMap (𝓞 I.F) (Fv I.F v)) m]
    exact congrFun (HeightOneSpectrum.algebraMap_adicCompletion ..) _
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hm, inv_one]

theorem Cst_not_mem (g1 g2 : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) (hv : ¬ IsTyped I.F g1 g2 v) :
    ((g1 * g2 : ℕ) : 𝓞 I.F) ∉ v.asIdeal := by
  intro h
  rw [Nat.cast_mul] at h
  exact hv (v.isPrime.mem_or_mem h)

open Classical in

def cElt (g1 g2 : ℕ) : Af I.F :=
  (⟨fun v => if IsTyped I.F g1 g2 v then 0 else (((g1 * g2 : ℕ) : Fv I.F v))⁻¹,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs with h
      · exact zero_mem _
      · exact Cst_inv_int I v _ (Cst_not_mem I g1 g2 v h)⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 I.F) => v.adicCompletion I.F)
      (fun v => v.adicCompletionIntegers I.F) Filter.cofinite)

open Classical in
theorem Cst_apply (g1 g2 : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) :
    cElt I g1 g2 v = if IsTyped I.F g1 g2 v then 0 else (((g1 * g2 : ℕ) : Fv I.F v))⁻¹ := rfl

theorem Cst_int (g1 g2 : ℕ) : cElt I g1 g2 ∈ Formalism.UG.intAd I.F := by
  classical
  intro v
  show cElt I g1 g2 v ∈ _
  rw [Cst_apply]
  split_ifs with h
  · exact zero_mem _
  · exact Cst_inv_int I v _ (Cst_not_mem I g1 g2 v h)

theorem Cst_natCast_apply (m : ℕ) (v : HeightOneSpectrum (𝓞 I.F)) : (m : Af I.F) v = (m : Fv I.F v) :=
  map_natCast (evalV I.F v) m

theorem Cst_sum_apply {ι : Type} (s : Finset ι) (f : ι → Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) :
    (∑ i ∈ s, f i) v = ∑ i ∈ s, f i v :=
  map_sum (evalV I.F v) f s

theorem Cst_gc (g1 g2 : ℕ) (h1 : g1 ≠ 0) (h2 : g2 ≠ 0) :
    ((g1 * g2 : ℕ) : Af I.F) * cElt I g1 g2 = 1 - ∑ p : TypP I.F g1 g2, chi I p.1 := by
  classical
  apply FiniteAdeleRing.ext
  intro v
  rw [Comp_mul_apply, Comp_sub_apply, Comp_one_apply, Cst_natCast_apply, Cst_sum_apply, Cst_apply]
  by_cases hv : IsTyped I.F g1 g2 v
  · have hmem : v ∈ typSet I.F g1 g2 := (mem_typSet I.F g1 g2 h1 h2 v).mpr hv
    rw [if_pos hv, mul_zero, Finset.sum_eq_single (⟨v, hmem⟩ : TypP I.F g1 g2)]
    · rw [Comp_chi_same, sub_self]
    · intro b _ hb
      exact Comp_chi_ne I b.1 v (fun h => hb (Subtype.ext h.symm))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
    · apply mul_inv_cancel₀
      intro h0
      have : ((g1 * g2 : ℕ) : I.F) = 0 := by
        have h3 : algebraMap I.F (Fv I.F v) ((g1 * g2 : ℕ) : I.F) = 0 := by rw [map_natCast]; exact h0
        exact (algebraMap I.F (Fv I.F v)).injective (by rw [h3, map_zero])
      exact (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero h1 h2)) this
    · intro p _
      refine Comp_chi_ne I p.1 v fun h => hv ?_
      rw [h]
      exact (mem_typSet I.F g1 g2 h1 h2 p.1).mp p.2

end PI.MassDataKppVolLemmas
