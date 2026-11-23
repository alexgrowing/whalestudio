import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.Cyc.FirstLevel

open Polynomial GlobalTheory.Cyc.IntBasis

variable {l : ℕ} [Fact l.Prime]

private theorem norm_primitiveRoot_sub_one' (ζ : Om l) (hζ : IsPrimitiveRoot ζ l) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1)) := by
  have h1 : IsPrimitiveRoot (algebraMap (Om l) (PadicComplex l) ζ) (l ^ 1) := by
    rw [pow_one]
    exact hζ.map_of_injective (algebraMap (Om l) (PadicComplex l)).injective
  have h2 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl _ h1
  have h3 : ‖algebraMap (Om l) (PadicComplex l) (ζ - 1)‖ = ‖ζ - 1‖ :=
    PadicComplex.norm_extends l (ζ - 1)
  rw [map_sub, map_one, h2] at h3
  rw [← h3]
  simp

theorem norm_term (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (h0 : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = (l : ℝ) ^ n ∧ ∀ a : ℕ, ‖z * (ζ - 1) ^ a‖ =
        (l : ℝ) ^ (((n * (l - 1) - a : ℤ) : ℝ) / ((l : ℝ) - 1)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l := by linarith
  have hm : (l : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K z hz h0
  refine ⟨n, hn, fun a => ?_⟩
  rw [norm_mul, norm_pow, hn, norm_primitiveRoot_sub_one' ζ hζ, ← Real.rpow_intCast,
    ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_add hl0]
  congr 1
  push_cast
  field_simp
  try ring

theorem term_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : ℕ → Om l) (hz : ∀ a, z a ∈ K0 K) (a : ℕ) (ha : a < l - 1) :
    ‖z a * (ζ - 1) ^ a‖ ≤ ‖∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine norm_le_norm_sum (Finset.range (l - 1)) (fun b => z b * (ζ - 1) ^ b) ?_ a
    (Finset.mem_range.2 ha)
  intro b hb c hc hbc hb0 hc0 heq
  have hb' : z b ≠ 0 := fun h => hb0 (by simp [h])
  have hc' : z c ≠ 0 := fun h => hc0 (by simp [h])
  have heq' : ‖z b * (ζ - 1) ^ b‖ = ‖z c * (ζ - 1) ^ c‖ := heq
  obtain ⟨nb, -, hnb⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z b) (hz b) hb'
  obtain ⟨nc, -, hnc⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ (z c) (hz c) hc'
  rw [hnb b, hnc c] at heq'
  have he := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 heq'.le)
    ((Real.rpow_le_rpow_left_iff hl1).1 heq'.ge)
  rw [div_left_inj' hm.ne'] at he
  have he' : nb * ((l : ℤ) - 1) - b = nc * ((l : ℤ) - 1) - c := by exact_mod_cast he
  rw [Finset.mem_range] at hb hc
  have hb2 : (b : ℤ) < (l : ℤ) - 1 := by omega
  have hc2 : (c : ℤ) < (l : ℤ) - 1 := by omega
  have hb3 : (0 : ℤ) ≤ b := by omega
  have hc3 : (0 : ℤ) ≤ c := by omega
  have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
  apply hbc
  rcases lt_trichotomy nb nc with h | h | h
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nb + 1 ≤ nc by omega) hm']
  · subst h
    have : (b : ℤ) = c := by linarith
    exact_mod_cast this
  · exfalso
    nlinarith [mul_le_mul_of_nonneg_right (show nc + 1 ≤ nb by omega) hm']

theorem coeff_le (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (z : Om l) (hz : z ∈ K0 K) (a : ℕ) (ha : a < l - 1) (h : ‖z * (ζ - 1) ^ a‖ ≤ 1) :
    ‖z‖ ≤ 1 := by
  by_cases h0 : z = 0
  · rw [h0, norm_zero]
    exact zero_le_one
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  obtain ⟨n, hn, hna⟩ := GlobalTheory.Cyc.FirstLevel.norm_term K ζ hζ z hz h0
  rw [hna a] at h
  have h' := (Real.rpow_le_rpow_left_iff hl1).1 (h.trans_eq (Real.rpow_zero (l : ℝ)).symm)
  rw [div_le_iff₀ hm, zero_mul] at h'
  have key : n * ((l : ℤ) - 1) - a ≤ 0 := by exact_mod_cast h'
  have ha' : (a : ℤ) < (l : ℤ) - 1 := by omega
  have hn0 : n ≤ 0 := by
    by_contra hc
    have hm' : (0 : ℤ) ≤ (l : ℤ) - 1 := by omega
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ n by omega) hm']
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le hn0

theorem exists_poly (K : FinExt l) (ζ : Om l) (hζ : IsPrimitiveRoot ζ l)
    (x : Om l) (hx : x ∈ Ks K 1) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l - 1 ∧ aeval ζ p = x := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have : NeZero l := ⟨by omega⟩
  have hint : IsIntegral (↥(K0 K)) ζ := by
    refine IsIntegral.of_pow (n := l) (by omega) ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  have hle : Ks K 1 ≤ (IntermediateField.adjoin (↥(K0 K)) {ζ}).restrictScalars ℚ_[l] := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      rw [IntermediateField.mem_restrictScalars]
      exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : ↥(K0 K))
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      have hy' : y ^ l = 1 := by simpa using hy
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy'
      rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  have hx' : x ∈ (IntermediateField.adjoin (↥(K0 K)) {ζ}).toSubalgebra :=
    (IntermediateField.mem_restrictScalars ℚ_[l]).1 (hle hx)
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx'
  obtain ⟨p, rfl⟩ := hx'
  have hmon := minpoly.monic hint
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly (↥(K0 K)) ζ).natDegree ≤ l - 1 := by
    have hdvd : minpoly (↥(K0 K)) ζ ∣ Polynomial.cyclotomic l (↥(K0 K)) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hζ.isRoot_cyclotomic (by omega)
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.cyclotomic_ne_zero l (↥(K0 K)))
    rwa [Polynomial.natDegree_cyclotomic, Nat.totient_prime (Fact.out : l.Prime)] at this
  refine ⟨p %ₘ minpoly (↥(K0 K)) ζ, ?_, ?_⟩
  · have hne : minpoly (↥(K0 K)) ζ ≠ 1 := by
      intro h
      rw [h, Polynomial.natDegree_one] at hpos
      exact lt_irrefl 0 hpos
    exact lt_of_lt_of_le (Polynomial.natDegree_modByMonic_lt p hmon hne) hdeg
  · exact Polynomial.aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

end GlobalTheory.Cyc.FirstLevel

open Polynomial GlobalTheory.Cyc.IntBasis in

theorem GlobalTheory.Cyc.integers_level_one_eq_sum_zeta_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : Om l), IsPrimitiveRoot ζ l → ∀ α : Om l, α ∈ Ks K 1 → ‖α‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ K0 K ∧ ‖y a‖ ≤ 1) ∧ α = ∑ a : Fin l, ζ ^ (a : ℕ) * y a := by
  intro l _ K ζ hζ α hα hα1
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨p, hpdeg, hp⟩ := GlobalTheory.Cyc.FirstLevel.exists_poly K ζ hζ α hα
  set q := Polynomial.taylor (1 : ↥(K0 K)) p with hq
  have hqdeg : q.natDegree < l - 1 := by
    rw [hq, Polynomial.natDegree_taylor]
    exact hpdeg
  let z : ℕ → Om l := fun b => ((q.coeff b : ↥(K0 K)) : Om l)
  have hzK : ∀ b, z b ∈ K0 K := fun b => (q.coeff b).2
  have hsum : α = ∑ b ∈ Finset.range (l - 1), z b * (ζ - 1) ^ b := by
    rw [← hp]
    have h1 : aeval ζ p = aeval (ζ - 1) q := by
      rw [hq, aeval_taylor']
      congr 1
      simp
    rw [h1, Polynomial.aeval_eq_sum_range' hqdeg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hzle : ∀ b, ‖z b‖ ≤ 1 := by
    intro b
    by_cases hb : b < l - 1
    · apply GlobalTheory.Cyc.FirstLevel.coeff_le K ζ hζ (z b) (hzK b) b hb
      calc ‖z b * (ζ - 1) ^ b‖ ≤ ‖∑ c ∈ Finset.range (l - 1), z c * (ζ - 1) ^ c‖ :=
            GlobalTheory.Cyc.FirstLevel.term_le K ζ hζ z hzK b hb
        _ = ‖α‖ := by rw [← hsum]
        _ ≤ 1 := hα1
    · have hc : q.coeff b = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [z, hc]
  let Q : (intRing (K0 K))[X] := ∑ b ∈ Finset.range (l - 1),
    Polynomial.C (⟨z b, ⟨hzK b, hzle b⟩⟩ : intRing (K0 K)) * (Polynomial.X - Polynomial.C 1) ^ b
  have hQdeg : Q.natDegree < l := by
    have : Q.natDegree ≤ l - 2 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro b hb
      rw [Finset.mem_range] at hb
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine Polynomial.natDegree_pow_le.trans ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
    omega
  have hQ : aeval ζ Q = α := by
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    rfl
  have hmem : ∀ s : intRing (K0 K), (s : Om l) ∈ K0 K ∧ ‖(s : Om l)‖ ≤ 1 := fun s => s.2
  refine ⟨fun a : Fin l => ((Q.coeff (a : ℕ) : intRing (K0 K)) : Om l),
    fun a => hmem _, ?_⟩
  rw [← hQ, Polynomial.aeval_eq_sum_range' hQdeg, Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, mul_comm]
  rfl
