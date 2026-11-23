import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresLeTwoMulOfSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnitsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexHigherUnitsSuccLeCardStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSquaresLeTwoMulUnitsSquaresStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.relIndex_higherUnits_succ_le_card K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := GlobalTheory.T.higherUnits_le_squares_higherUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := GlobalTheory.T.index_squares_le_two_mul_units_squares (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
