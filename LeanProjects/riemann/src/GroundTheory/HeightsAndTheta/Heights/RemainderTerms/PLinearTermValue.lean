import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def rowOne (r : ℕ) : Fin r → ℕ := fun i => if (i : ℕ) = 0 then 1 else 0

theorem partitionsOf_one (r : ℕ) (hr : 1 ≤ r) : partitionsOf r 1 = {rowOne r} := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  ext lam
  rw [mem_partitionsOf_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, ha⟩
    rw [Fin.sum_univ_succ] at hs
    have hle : ∀ i : Fin r', lam i.succ ≤ lam 0 := fun i => ha (Fin.zero_le _)
    have h0 : lam 0 = 1 := by
      by_contra h
      have hz : lam 0 = 0 := by omega
      have : ∑ i : Fin r', lam i.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by have := hle i; omega
      omega
    have hrest : ∑ i : Fin r', lam i.succ = 0 := by omega
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rowOne, h0]
    · have := Finset.sum_eq_zero_iff.mp hrest j (Finset.mem_univ j)
      simp [rowOne, this]
  · rintro rfl
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Fin.sum_univ_succ]
      simp [rowOne]
    · simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega)

theorem schur_rowOne (σ : Type*) [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 1 ≤ r) :
    schur σ (rowOne r) = ∑ i : σ, X i := by
  unfold schur
  rw [Matrix.det_of_isUpperTriangular]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Fin.prod_univ_succ]
    have h1 : ∏ i : Fin r', Matrix.of (fun i j : Fin (r' + 1) =>
        completeSymmetric σ ((rowOne (r' + 1) i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
        i.succ i.succ = 1 :=
      Finset.prod_eq_one fun i _ => by simp [rowOne, completeSymmetric_zero]
    rw [h1, mul_one]
    simp [rowOne, completeSymmetric, hsymm_one]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply completeSymmetric_neg
    have : (j : ℕ) < i := hij
    simp only [rowOne]
    split_ifs with h
    · omega
    · push_cast; omega

end

end Top

open Top MvPolynomial Finset

noncomputable section

theorem LinearTermValue.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) :
    LinearTermValue.Statement := by
  intro r a hr ha Q hQ
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a .last
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA 1 (r + a)
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hJ := fibreDegree_eq hF hCI hV 1 r a .last hr ha κ hκ c0 hInt
  have hGF : (1 : RootRing 1 (r + a)) * restPolynomial 1 r a .last =
      gmf 1 r a .last 0 (1 * (r * a) + 1) := by
    simp [gmf, extraFactor, restPolynomial]
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ 1 le_rfl (by omega) 0 1 (isHomogeneous_one _ _)
  have hPeq : P = gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF 1 r a .last κ hκ 0 _)]
  have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  have hres := restrict_gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) 0
    (fun σ hσ => absurd (Subsingleton.elim σ 0) hσ) (by simp [herase])
  have hm : mstar 1 r a 0 (1 * (r * a) + 1) 0 = fun _ => r * a + 1 := by
    funext σ
    rw [Subsingleton.elim σ 0]
    simp [mstar, herase]
  rw [hm, herase, Finset.prod_empty, Pi.zero_apply,
    toN_blockOut r a .last κ 0 (r * a + 1) 1 (by omega), partitionsOf_one r hr,
    Finset.sum_singleton, schur_rowOne _ r hr] at hres
  have hmult : (Nat.multinomial Finset.univ (fun _ : Fin 1 => r * a + 1) : ℚ) = 1 := by
    rw [multinomial_const]
    have : ((r * a + 1).factorial : ℚ) ≠ 0 := by positivity
    simp [this]
  rw [hmult] at hres
  set b := blockCoeff 0 (r * a + 1) (fun i => a + rowOne r i) with hb
  have hb' : b = numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) := by
    rw [hb, blockCoeff, if_pos rfl, if_neg (by omega)]
    have h := hCI r (fun i => a + rowOne r i) (fun i j hij => by
      simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega))
    have hs : ∑ i, (a + rowOne r i) = r * a + 1 := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Finset.sum_add_distrib, Fin.sum_univ_succ]
      simp [rowOne, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hs] at h
    exact h
  have hS'eq : S' = C (κ * b) * X (⟨0, by omega⟩ : Fin (r + a)) := by
    apply Flag.powerSumHom_injective
    rw [hS', hPeq, hres]
    simp only [powerSumHom, map_mul, aeval_C, aeval_X, algebraMap_eq, psum, map_sum,
      SmallBlock.sign, map_one, one_mul, one_smul, zero_add, pow_one]
    first | done | ring
  rw [hS'eq, one_mul] at hI
  rw [hI, hJ]
  simp only [coeff_C_mul, coeff_X, mul_one]
  rw [← hb']
  have h01 : (⟨1 - 1, by omega⟩ : Fin (r + a)) = ⟨0, by omega⟩ := rfl
  have hfac : ((r * a).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp only [if_true, mul_one, one_mul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
