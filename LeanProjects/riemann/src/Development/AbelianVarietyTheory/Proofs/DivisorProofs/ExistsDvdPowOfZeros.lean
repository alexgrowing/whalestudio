import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.HyperplaneFactor

theorem eval_lin {K : Type} [Field K] {N : ℕ} (x : Fin 1 × Fin N → K) (y : Fin N → K) :
    eval x (lin y) = ∑ j, x (0, j) * y j := by
  simp [lin]

theorem coeff_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) (j : Fin N) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (lin y) = y j := by
  classical
  rw [lin, coeff_sum]
  simp only [mul_comm (X _) (C _), coeff_C_mul, coeff_X', Finsupp.single_left_inj (one_ne_zero' ℕ)]
  simp

theorem isHomogeneous_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X K _).mul (isHomogeneous_C _ _)

theorem irreducible_lin {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : Irreducible (lin y) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have h0 : lin y ≠ 0 := fun h => hj (by
    have := coeff_lin y j
    rw [h, coeff_zero] at this
    exact this.symm)
  refine irreducible_of_totalDegree_eq_one ((isHomogeneous_lin y).totalDegree h0) fun x hx => ?_
  have hd := hx (Finsupp.single (0, j) 1)
  rw [coeff_lin] at hd
  exact isUnit_of_dvd_unit hd (IsUnit.mk0 _ hj)

theorem exists_dvd_pow_of_zeros {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {a b : MvPolynomial (Fin 1 × Fin N) K}
    (h : ∀ x, eval x a = 0 → eval x b = 0) : ∃ n : ℕ, a ∣ b ^ n := by
  have hb : b ∈ (Ideal.span {a}).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have h1 := hx a (Ideal.subset_span rfl)
    have e : ∀ p : MvPolynomial (Fin 1 × Fin N) K, aeval x p = eval x p := fun p =>
      DFunLike.congr_fun (coe_aeval_eq_eval x) p
    rw [e] at h1
    change aeval x b = 0
    rw [e]
    exact h x h1
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem eq_C_mul_prod_lin : ∀ (K : Type) [Field K] [IsAlgClosed K] (N δ m : ℕ) (g : MvPolynomial (Fin 1 × Fin N) K)
    (y : Fin m → Fin N → K), g.IsHomogeneous δ → NoSquare g → (∀ q, y q ≠ 0) →
    (∀ q q' (c : K), y q' = c • y q → q = q') →
    (∀ ξ : Fin N → K, eval (fun p => ξ p.2) g = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0) →
    m = δ ∧ ∃ c : K, c ≠ 0 ∧ g = C c * ∏ q, lin (y q) := by
  intro K _ _ N δ m g y hg hns hy hinj hz
  classical
  have hz' : ∀ x : Fin 1 × Fin N → K, eval x g = 0 ↔ ∃ q, eval x (lin (y q)) = 0 := by
    intro x
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz fun j => x (0, j)
    simp only [e] at h1
    simpa only [eval_lin] using h1
  have irr : ∀ q, Irreducible (lin (y q)) := fun q => irreducible_lin (hy q)
  have dvdg : ∀ q, lin (y q) ∣ g := fun q => by
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := lin (y q)) (b := g) fun x hx => (hz' x).2 ⟨q, hx⟩
    exact (irr q).prime.dvd_of_dvd_pow hn
  have nondvd : ∀ q q', q ≠ q' → ¬ lin (y q) ∣ lin (y q') := by
    intro q q' hne hd
    obtain ⟨a, ha⟩ := (irr q).associated_of_dvd (irr q') hd
    obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
    rw [ht, mul_comm] at ha
    refine hne (hinj q q' t (funext fun j => ?_))
    have h1 := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) ha
    rw [coeff_C_mul, coeff_lin, coeff_lin] at h1
    simpa using h1.symm
  have Pdvd : (∏ q, lin (y q)) ∣ g := Finset.prod_dvd_of_isRelPrime
    (fun q _ q' _ hne => (irr q).isRelPrime_iff_not_dvd.2 (nondvd q q' hne)) fun q _ => dvdg q
  obtain ⟨h, hh⟩ := Pdvd
  have h0 : h ≠ 0 := fun e => hns.1 (by rw [hh, e, mul_zero])
  have hu : IsUnit h := by
    by_contra hu
    obtain ⟨p, pirr, pd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := g) (b := ∏ q, lin (y q)) fun x hx => by
      obtain ⟨q, hq⟩ := (hz' x).1 hx
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hq
    have pg : p ∣ g := hh ▸ pd.mul_left _
    obtain ⟨q, -, hq⟩ := (Prime.exists_mem_finset_dvd pirr.prime (pirr.prime.dvd_of_dvd_pow (pg.trans hn)))
    have hl : lin (y q) ∣ p := ((pirr.associated_of_dvd (irr q) hq).symm).dvd
    refine hns.2 (y q) (hy q) ?_
    rw [hh, pow_two]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (hl.trans pd)
  obtain ⟨c, hc, hcC⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hgC : g = C c * ∏ q, lin (y q) := by rw [hh, hcC, mul_comm]
  have hP : (∏ q, lin (y q)).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun q => lin (y q)) (fun _ => 1) fun q _ => isHomogeneous_lin (y q)
  have hgm : g.IsHomogeneous m := by
    rw [hgC]
    simpa using (isHomogeneous_C (Fin 1 × Fin N) c).mul hP
  exact ⟨(hgm.totalDegree hns.1).symm.trans (hg.totalDegree hns.1), c, hc.ne_zero, hgC⟩

end GlobalTheory.HSChoice.HyperplaneFactor
