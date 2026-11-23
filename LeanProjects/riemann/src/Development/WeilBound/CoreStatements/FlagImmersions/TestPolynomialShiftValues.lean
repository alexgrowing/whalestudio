import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.WeylPolynomialAlgebra

noncomputable section

namespace RootFieldNumerics.TF

section A
open Finset MvPolynomial Formalism.L2.Geo Formalism.L2.Geo.WeylPolynomialAlgebra

theorem jPos (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    0 < (-1) ^ (idxS Ψ N j).card * PhiL j (a0n Ψ N j) (∏ t ∈ idxS Ψ N j, ell t) := by
  set n := a0n Ψ N j
  set k := (idxS Ψ N j).card with hkdef
  set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef
  have hD : D = n + k := dim_split j hj
  set fib : Formalism.ShimuraLimitIdentity.Pol Ψ N := ∏ t ∈ idxS Ψ N j, ell t with hfib

  set K0 : ℝ := (D.factorial : ℝ) * (∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) *
    (∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) / (D.choose n : ℝ) with hK0
  have hpos : ∀ s : Finset (Ψ × Fin N × Fin N), (∀ t ∈ s, t.2.1 < t.2.2) →
      0 < ∏ t ∈ s, 1 / ((t.2.2 : ℝ) - t.2.1) := by
    intro s hs
    refine Finset.prod_pos (fun t ht => ?_)
    have : (t.2.1 : ℝ) < t.2.2 := by exact_mod_cast (hs t ht)
    exact one_div_pos.mpr (by linarith)
  have hK0pos : 0 < K0 := by
    have h1 := hpos (idxS Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h2 := hpos (idxC Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h3 : (0 : ℝ) < (D.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have h4 : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos D
    positivity

  have hPhi : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) =
      K0 * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    have hw := weyl_coeff j ν n k hD hkdef.symm
    rw [PhiL_apply, eval_fib]
    have hc : (D.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have e : ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1) =
        (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)) * ∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1) := by
      rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e] at hw
    rw [hK0]
    field_simp
    linarith [hw]

  have hApol : ∀ ν : Ψ → Fin N → ℝ, apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) =
      (k.factorial : ℝ) * (-1) ^ k * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    show apol fib _ = _
    rw [linRoot_eq_smul, apol_pow fib k (fib_homog j), eval_fib, eval_fib]
    have e : ∏ t ∈ idxS Ψ N j, (-ν t.1 t.2.1 - -ν t.1 t.2.2) =
        (-1) ^ k * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) := by
      rw [hkdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e]; ring

  set c : ℝ := K0 * (-1) ^ k / (k.factorial : ℝ) with hc
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hagree : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = c * apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) := by
    intro ν
    rw [hPhi, hApol, hc]
    have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    exact mul_eq_sign_rearrange K0 _ _ _ hkf h1

  have hpol := polarization (fun t => (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) (idxS Ψ N j)
  have hsumS : ∀ S : Finset (Ψ × Fin N × Fin N), (∑ t ∈ S, (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) =
      Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) := by
    intro S; rw [linRoot_sum]; exact Finset.sum_congr rfl (fun t _ => (linRoot_nuT t).symm)
  have hcast : ∀ S : Finset (Ψ × Fin N × Fin N), ((-1 : Formalism.ShimuraLimitIdentity.Pol Ψ N) ^ ((idxS Ψ N j).card - S.card)) =
      C ((-1 : ℝ) ^ ((idxS Ψ N j).card - S.card)) := by
    intro S; rw [map_pow, map_neg, map_one]
  rw [← hfib] at hpol
  simp only [hsumS, hcast] at hpol
  rw [show (((idxS Ψ N j).card.factorial : ℕ) : Formalism.ShimuraLimitIdentity.Pol Ψ N) = C ((k.factorial : ℕ) : ℝ) by
    rw [map_natCast]] at hpol
  have hP := congrArg (PhiL j n) hpol
  have hA := congrArg (apolL fib) hpol
  rw [PhiL_C_mul, map_sum] at hP
  rw [apolL_C_mul, map_sum] at hA
  simp only [PhiL_C_mul, apolL_C_mul, ← hkdef, hagree] at hP hA
  have hmain : PhiL j n fib = c * apolL fib fib := by
    have e1 : ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
        (c * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k)) =
        c * ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
          apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun S _ => ?_); ring
    rw [e1, ← hA] at hP
    have : (k.factorial : ℝ) * PhiL j n fib = (k.factorial : ℝ) * (c * apolL fib fib) := by rw [hP]; ring
    exact mul_left_cancel₀ hkf this
  have hapos : 0 < apolL fib fib := apol_self_pos fib (fib_ne_zero j)
  rw [hmain, hc]
  have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have e : (-1 : ℝ) ^ k * (K0 * (-1) ^ k / (k.factorial : ℝ) * apolL fib fib) =
      ((-1 : ℝ) ^ k * (-1) ^ k) * (K0 / (k.factorial : ℝ) * apolL fib fib) := by ring
  rw [e, h1]
  positivity

end A

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open Formalism.L2.Geo.WeylPolynomialAlgebra Formalism.L2.Geo.BlockVandermondeForms

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem fib_eq' (j : ℕ) :
    (fibClass j : RP Ψ N) = C ((-1 : ℝ) ^ (idxS Ψ N j).card) * ∏ t ∈ idxS Ψ N j, ell t := by
  rw [map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  unfold fibClass idxS ell
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl (fun ab _ => ?_)
  split_ifs
  · simp
  · rfl

theorem degFl_eq (F : RP Ψ N) : degFl F = Formalism.L2.Geo.degFlL Ψ N F := by
  rw [Formalism.L2.Geo.degFlL_apply]; rfl

theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  rw [degFl_eq, degFl_eq, degFlL_C_mul]

theorem mu_sub (j : ℕ) : ∃ c : RP Ψ N, (muSmall j : RP Ψ N) - Formalism.L2.Geo.a0Mu j = c * ∑ τ, pk τ 1 := by
  unfold muSmall
  split_ifs
  · exact ⟨0, by rw [zero_mul, sub_eq_zero]; rfl⟩
  · refine ⟨-1, ?_⟩
    unfold Formalism.L2.Geo.a0Mu Formalism.L2.Geo.smallBlock pkLow pk
    rw [← neg_add', neg_one_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simp only [pow_one, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (i : ℕ) < j
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]

theorem deg_mu (j n : ℕ) (G : RP Ψ N) :
    degFl (muSmall j ^ n * G) = degFl (Formalism.L2.Geo.a0Mu j ^ n * G) := by
  obtain ⟨c, hc⟩ := mu_sub (Ψ := Ψ) (N := N) j
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (muSmall j : RP Ψ N) (Formalism.L2.Geo.a0Mu j) n
  have e : (muSmall j : RP Ψ N) ^ n * G = Formalism.L2.Geo.a0Mu j ^ n * G + ∑ τ, pk τ 1 * (c * d * G) := by
    rw [← Finset.sum_mul]
    rw [hc] at hd
    linear_combination G * hd
  rw [e, degFl_eq, degFl_eq, map_add, map_sum, Finset.sum_eq_zero, add_zero]
  intro τ _
  exact Formalism.L2.Geo.flag_integral_kills_power_sums Ψ N τ 1 le_rfl _

theorem testDeg_pos (j : ℕ) (hj : j ≤ N) : 0 < testDeg Ψ N j := by
  unfold testDeg
  rw [deg_mu, fib_eq', mul_left_comm, degFl_C_mul, degFl_eq]
  exact jPos Ψ N j hj

theorem d_fib (τ : Ψ) (j : ℕ) (S : Finset (Fin N))
    (hS : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ S ↔ b ∈ S)) :
    dS τ S (fibClass j : RP Ψ N) = 0 := by
  unfold fibClass
  refine d_prod_zero _ _ _ (fun σ _ => d_prod_zero _ _ _ (fun ab hab => ?_))
  have h := hS _ _ (Finset.mem_filter.mp hab).2.2
  rw [map_sub, dS_X, dS_X]
  simp only [h, sub_self]

theorem d_sum (τ : Ψ) (S T : Finset (Fin N)) :
    dS τ S (∑ σ : Ψ, ∑ i ∈ T, (X (σ, i) : RP Ψ N)) = C (((T.filter (· ∈ S)).card : ℕ) : ℝ) := by
  rw [map_sum, Finset.sum_eq_single τ]
  · rw [map_sum]
    simp only [dS_X, true_and]
    rw [Finset.sum_boole, map_natCast]
  · intro σ _ hσ
    rw [map_sum]
    simp [dS_X, hσ]
  · simp

theorem deg_d_test (τ : Ψ) (j : ℕ) (S : Finset (Fin N)) (c : ℝ)
    (hS : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ S ↔ b ∈ S))
    (hc : dS τ S (muSmall j : RP Ψ N) = C c) :
    degFl (∑ i ∈ S, pderiv (τ, i) (testPoly j : RP Ψ N)) = ((dimX Ψ N j : ℝ) + 1) * c * testDeg Ψ N j := by
  rw [← dS_apply]
  unfold testPoly testDeg
  rw [Derivation.leibniz, Derivation.leibniz_pow, hc, d_fib τ j S hS, ← degFl_C_mul]
  congr 1
  simp only [smul_zero, zero_add, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, map_mul, map_add, map_one,
    map_natCast]
  push_cast
  ring

theorem mu_homog' (j : ℕ) : (muSmall j : RP Ψ N).IsHomogeneous 1 := by
  unfold muSmall
  split_ifs
  · exact IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => isHomogeneous_X ℝ _))
  · refine IsHomogeneous.neg (IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => ?_)))
    rw [pow_one]; exact isHomogeneous_X ℝ _

theorem test_homog (j : ℕ) (hj : j ≤ N) : (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
  unfold testPoly
  rw [fib_eq']
  have h := ((mu_homog' (Ψ := Ψ) (N := N) j).pow (dimX Ψ N j + 1)).mul
    ((isHomogeneous_C _ ((-1 : ℝ) ^ (idxS Ψ N j).card)).mul (fib_homog (Ψ := Ψ) (N := N) j))
  have hD : dimFl Ψ N = dimX Ψ N j + (idxS Ψ N j).card := dim_split j hj
  have e : 1 * (dimX Ψ N j + 1) + (0 + (idxS Ψ N j).card) = dimFl Ψ N + 1 := by omega
  rwa [e] at h

end RootFieldNumerics.TF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics.TF Formalism.L2.Geo.BlockVandermondeForms in
theorem RootFieldNumerics.test_polynomial_shift_values : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  intro Ψ _ _ N j _ hjN
  have hlow : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) →
      (a ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) ↔
        b ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)) := by
    intro a b h; simpa using h
  have hall : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) →
      (a ∈ (Finset.univ : Finset (Fin N)) ↔ b ∈ (Finset.univ : Finset (Fin N))) := by
    intro a b _; simp
  have c1 : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := card_top N j hjN.le
  have c2 : (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := card_smallBlock N j
  refine ⟨test_homog j hjN.le, testDeg_pos j hjN.le, fun h τ => ⟨?_, ?_⟩, fun h τ => ⟨?_, ?_⟩⟩
  · unfold Sh
    rw [deg_d_test τ j _ 0 hlow]
    · ring
    · unfold muSmall
      rw [if_pos h, d_sum, Finset.filter_false_of_mem]
      · simp
      · intro x hx; simpa using hx
  · unfold Tot
    rw [deg_d_test τ j _ ((N - j : ℕ) : ℝ) hall]
    unfold muSmall
    rw [if_pos h, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c2]
  · unfold Sh
    rw [deg_d_test τ j _ (-(j : ℝ)) hlow]
    · ring
    · unfold muSmall pkLow
      simp only [pow_one]
      rw [if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ hx => hx), c1, map_neg]
  · unfold Tot
    rw [deg_d_test τ j _ (-(j : ℝ)) hall]
    · ring
    · unfold muSmall pkLow
      simp only [pow_one]
      rw [if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c1, map_neg]
