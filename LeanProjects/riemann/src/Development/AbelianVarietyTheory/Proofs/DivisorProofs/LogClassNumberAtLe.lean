import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetDecoSetLatticeReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMovePreservingLocalParts
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnClassLog

theorem log_le_of_count (h f n N g₀ g₁ T : ℕ) (rd L : ℝ) (hf : 1 ≤ f) (hn : 1 ≤ n) (hnN : n ≤ N) (hT : 1 ≤ T) (hrd : 0 < rd)
    (hL : 1 ≤ L) (hrdL : Real.log rd ≤ L) (hfN : (f : ℝ) * N ≤ Real.exp L) (hg₀ : Real.exp L ≤ g₀) (hg₁ : 1 ≤ g₁)
    (hh : (h : ℝ) ≤ (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2)) ^ (3 * (2 * f) * n ^ 2) *
      ((g₀ : ℝ) * g₁ * T) ^ (f * (n * n))) :
    Real.log h ≤ 55 * (f : ℝ) * (N : ℝ) ^ 2 * Real.log ((g₀ : ℝ) * g₁ * T) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hg₁' : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have he : 0 < Real.exp L := Real.exp_pos L
  have hg0 : (0 : ℝ) < g₀ := lt_of_lt_of_le he hg₀
  have hG : Real.exp L ≤ (g₀ : ℝ) * g₁ * T := by
    calc Real.exp L ≤ g₀ := hg₀
      _ = (g₀ : ℝ) * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  set G : ℝ := (g₀ : ℝ) * g₁ * T with hGd
  have hGp : 0 < G := lt_of_lt_of_le he hG
  have hLG : L ≤ Real.log G := (Real.le_log_iff_exp_le hGp).2 hG
  have hlG : 0 ≤ Real.log G := by linarith
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hrd' : rd ≤ Real.exp L := (Real.log_le_iff_le_exp hrd).1 hrdL
  have hfn : (f : ℝ) * n ≤ Real.exp L := le_trans (by gcongr) hfN
  have hn2 : (n : ℝ) ≤ Real.exp L := le_trans (by nlinarith) hfn
  have h12 : (12 : ℝ) ≤ Real.exp L ^ 3 := by
    have h1 : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.2 hL
    have h2 : (2.7 : ℝ) ≤ Real.exp L := by linarith [Real.exp_one_gt_d9]
    calc (12 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  set A : ℝ := 3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * rd ^ 2) with hA
  have hAp : 0 < A := by rw [hA]; push_cast; positivity
  have hA9 : A ≤ G ^ 9 := by
    calc A = 12 * ((f : ℝ) * n) ^ 2 * (n : ℝ) ^ 2 * rd ^ 2 := by rw [hA]; push_cast; ring
      _ ≤ Real.exp L ^ 3 * Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp L ^ 2 := by gcongr
      _ = Real.exp L ^ 9 := by ring
      _ ≤ G ^ 9 := by gcongr
  have hfin : (h : ℝ) ≤ G ^ (55 * f * n ^ 2) := by
    calc (h : ℝ) ≤ A ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := hh
      _ ≤ (G ^ 9) ^ (3 * (2 * f) * n ^ 2) * G ^ (f * (n * n)) := by gcongr
      _ = G ^ (55 * f * n ^ 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  calc Real.log h ≤ Real.log (G ^ (55 * f * n ^ 2)) := Real.log_le_log (by exact_mod_cast hpos) hfin
    _ = 55 * (f : ℝ) * (n : ℝ) ^ 2 * Real.log G := by rw [Real.log_pow]; push_cast; ring
    _ ≤ _ := by gcongr

theorem fibre_bound_le {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (u : Pr.Word) (n : ℕ) (hn : 1 ≤ n)
    (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (hSG : SG = Pr.vGs) :
    (∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n * n) ≤
      (Pr.g 0 * Pr.g 1 * Pr.T u) ^ (X.f * (n * n)) := by
  classical
  subst hSG
  have hT : ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n ≤ Pr.T u ^ (X.f * (n * n)) := by
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vT_norm u P hP']), Finset.prod_const, hP.vT_card, ← pow_mul]
    exact Nat.pow_le_pow_right (hP.T_prime u).pos (by rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.le_mul_self n))
  have hg : ∀ i, ∏ w ∈ Pr.vG i, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g i ^ (X.f * (n * n)) := by
    intro i
    rw [Finset.prod_congr rfl (fun P hP' => by rw [hP.vG_norm i P hP']), Finset.prod_const, hP.vG_card, ← pow_mul, mul_comm]
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := by
    rw [Finset.disjoint_left]
    intro w h0 h1
    exact hP.g_ne ((hP.vG_norm 0 w h0).symm.trans (hP.vG_norm 1 w h1))
  have hU : ∏ w ∈ Pr.vGs, Ideal.absNorm w.asIdeal ^ (n * n) = Pr.g 0 ^ (X.f * (n * n)) * Pr.g 1 ^ (X.f * (n * n)) := by
    rw [← hg 0, ← hg 1, ← Finset.prod_union hd]
    unfold Primes.vGs
    congr
  rw [hU, mul_pow, mul_pow, mul_comm]
  exact Nat.mul_le_mul_left _ hT

end GlobalTheory.ColumnClassLog
