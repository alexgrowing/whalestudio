import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem intCapP : IntCapP := by
  intro O K _ _ _ hinj k ν F hF hco
  obtain ⟨G, hG⟩ : F ∈ Set.range (map (algebraMap O K) : MvPolynomial (Fin k × Fin k) O →+* _) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨u, hu, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact hco u
  subst hG
  have hcomm : ∀ (l j : Fin k) (p : MvPolynomial (Fin k × Fin k) O),
      map (algebraMap O K) (colAddGen O l j p) = colAddGen K l j (map (algebraMap O K) p) := by
    intro l j p
    induction p using MvPolynomial.induction_on
    next a => simp [colAddGen]
    next p q hp hq => simp only [map_add, hp, hq]
    next p x hp =>
      simp only [map_mul, hp, map_X]
      congr 1
      simp only [colAddGen, aeval_X]
      split_ifs <;> simp
  refine Submodule.mem_map.mpr ⟨G, ?_, ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero, AlgHom.toLinearMap_apply, mem_weightedHomogeneousSubmodule] at hF ⊢
    obtain ⟨h1, h2⟩ := hF
    refine ⟨?_, ?_⟩
    · intro d hd
      exact h1 (by rw [coeff_map]; exact fun h0 => hd ((map_eq_zero_iff _ hinj).mp h0))
    · intro l j hlj
      apply MvPolynomial.map_injective _ hinj
      rw [hcomm, map_rename, h2 l j hlj]
  · first
      | rfl
      | simp [MvPolynomial.mapAlgHom]

theorem qa_nuNext_add {n : ℕ} (ν ν' : Fin n → ℕ) (s : Fin n) : nuNext (ν + ν') s = nuNext ν s + nuNext ν' s := by
  unfold nuNext
  split_ifs <;> simp

theorem qa_nuNext_le {n : ℕ} (ν : Fin n → ℕ) (h : Antitone ν) (s : Fin n) : nuNext ν s ≤ ν s := by
  unfold nuNext
  split_ifs with hs
  · exact h (Fin.le_def.2 (Nat.le_succ _))
  · exact Nat.zero_le _

theorem hwMulP : HwMulP := by
  intro A _ k ν ν' hν hν'
  refine ⟨?_, ?_⟩
  · simp only [hw, ← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    congr 1
    rw [qa_nuNext_add, Pi.add_apply]
    have h1 := qa_nuNext_le ν hν s
    have h2 := qa_nuNext_le ν' hν' s
    omega
  · have key : ∀ (m : ℕ) (h1 : m ≤ k) (h2 : m ≤ k), eval (idPoint A k k) (lpMinor A m h1 h2) = 1 := by
      intro m h1 h2
      rw [lpMinor, RingHom.map_det]
      convert (Matrix.det_one : (1 : Matrix (Fin m) (Fin m) A).det = 1)
      ext p q
      simp [idPoint, Matrix.one_apply, Fin.ext_iff]
    simp only [hw, map_prod, map_pow, key, one_pow, Finset.prod_const_one]

end Formalism.MainNotions.flipOneThree.Pf

end
