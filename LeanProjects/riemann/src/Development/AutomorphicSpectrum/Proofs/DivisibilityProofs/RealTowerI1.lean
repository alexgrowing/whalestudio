import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linA_eq (c : Option (Ψ × Fin N) → ℝ) :
    linA (fun τ i => c (some (τ, i))) (-c none) = -∑ x, C (c x) * X x := by
  rw [Fintype.sum_option]
  simp only [linA, toA, linRoot, map_neg, map_sum, map_mul, rename_C, rename_X, neg_add_rev, C_neg]
  simp only [Prod.mk.eta]
  ring

def scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) : MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  ∑ m ∈ Q.support, monomial m (u ^ m none * coeff m Q)

theorem coeff_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    coeff m (scaleNone u Q) = u ^ m none * coeff m Q := by
  classical
  rw [scaleNone, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' Q.support m]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem eval_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (c : Option (Ψ × Fin N) → ℝ) :
    eval c (scaleNone u Q) = eval (fun o : Option (Ψ × Fin N) => o.elim (u * c none) fun p => c (some p)) Q := by
  rw [scaleNone, map_sum, eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Fintype.prod_option, Option.elim, mul_pow]
  ring

theorem abs_le_coeff (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ)
    (h : ∀ (lam : Wt Ψ N) (s : ℝ), (n : ℝ) * Φ (linA lam s ^ d) = eval (PB.gapS (fun x => lam x.1 x.2) (s / k)) Q)
    (m : Option (Ψ × Fin N) →₀ ℕ) (hm : m.degree = d) :
    |Φ (monomial m 1)| ≤ |coeff m (PB.toWtS Q)| := by
  obtain ⟨Pl, -, hev, -, hle⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Option (Ψ × Fin N)) d Φ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set u : ℝ := -(k : ℝ)⁻¹ with hu
  have heq : C (n : ℝ) * Pl = scaleNone u (PB.toWtS Q) := by
    refine MvPolynomial.funext fun c => ?_
    have hs : -c none / (k : ℝ) = u * c none := by rw [hu]; ring
    rw [eval_scaleNone, map_mul, eval_C, hev, ← linA_eq, h, PB.eval_toWtS_gapS, hs]
  have hco := congrArg (coeff m) heq
  rw [coeff_C_mul, coeff_scaleNone] at hco
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_neg, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_le_one_of_one_le₀ hkR
  calc |Φ (monomial m 1)| ≤ |coeff m Pl| := hle m hm
    _ ≤ (n : ℝ) * |coeff m Pl| := le_mul_of_one_le_left (abs_nonneg _) hnR
    _ = |(n : ℝ) * coeff m Pl| := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
    _ = |u| ^ m none * |coeff m (PB.toWtS Q)| := by rw [hco, abs_mul, abs_pow]
    _ ≤ |coeff m (PB.toWtS Q)| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hu1)

theorem PP_monomial_of_ne (II : IntersectionSystem) (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ)
    (hm : m.degree ≠ dimFl Ψ N + 1) : M.PP II (monomial m 1) = 0 := by
  have h1 : (monomial m 1 : RPA Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ m := by simp
  rw [h1, RootModel.PP, Module.Basis.constr_basis]
  have h2 : (fun t => M.arMono II t m) = fun _ => 0 := by
    funext t
    simp [RootModel.arMono, hm]
  rw [h2]
  exact tendsto_const_nhds.limUnder_eq

theorem tower_I1_of_reference_linked : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N)
    (R : RealTower T), R.RefLinked II → T.I1 II := by
  intro hCo hAg hI II hII Ψ _ _ N T R hL
  obtain ⟨Cl, thH, Pfix, hth, hlink⟩ := hL
  have hpos : ∀ c, 0 < (R.Sys c).t₀ := fun c => ((R.Sys c).reg none).1
  choose C₂ hC₂ using fun c => hCo hI (dimFl Ψ N) N Ψ (R.Sys c) (thH c) (hth c)
  set A : ℝ := ∑ c, ∑ m ∈ (Pfix c).support, |coeff m (Pfix c)| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAle : ∀ c m, |coeff m (Pfix c)| ≤ A := by
    intro c m
    by_cases hm : m ∈ (Pfix c).support
    · calc |coeff m (Pfix c)| ≤ ∑ m ∈ (Pfix c).support, |coeff m (Pfix c)| :=
            Finset.single_le_sum (f := fun m => |coeff m (Pfix c)|) (fun _ _ => abs_nonneg _) hm
        _ ≤ A := Finset.single_le_sum (f := fun c => ∑ m ∈ (Pfix c).support, |coeff m (Pfix c)|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c)
    · rw [notMem_support_iff.1 hm, abs_zero]
      exact hA0
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hS0 : 0 ≤ ∑ c, |C₂ c| * |Cl| := Finset.sum_nonneg fun _ _ => by positivity
  unfold RootTower.I1
  refine ⟨A / Real.log 2 + ∑ c, |C₂ c| * |Cl|, fun B hB c m => ?_⟩
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log two_pos (by exact_mod_cast hB)
  have hlog0 : 0 ≤ Real.log B := hl2.le.trans hlogB
  by_cases hm : m.degree = dimFl Ψ N + 1
  · obtain ⟨C₃, s₀, -, hag⟩ := hAg hI _ _ (R.Sys c) 0 (hpos c)
    have htend := (hag II hII _ _ _ (R.tie B c).Re).1
    have hnum := GlobalTheory.T.real_tower_arith_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c)
    have hle := abs_le_coeff (dimFl Ψ N + 1) ((T.M B c).PP II) (R.n c) (T.M B c).kA (hnum 0 0).1
      (T.M B c).kA_pos ((R.tie B c).Re.PB II) (fun lam s => ((hnum lam s).2.2 htend (hpos c)).2) m hm
    obtain ⟨K, iK, ι, iι, P, Re, Re', Sf, α, H, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlink B hB c
    have hd := ((hC₂ c II hII K ι P Re).2 Re' Sf α H h3 h4 h5 h6 h7 h8).1 m
    rw [h1, h2] at hd
    have hsum0 : 0 ≤ ∑ p ∈ Sf, α p * Real.log p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (h4 p hp).2 (Real.log_natCast_nonneg p)
    have hd2 : |coeff m ((R.tie B c).Re.PBs II) - coeff m (Pfix c)| ≤ |C₂ c| * |Cl| * Real.log B := by
      calc _ ≤ C₂ c * ∑ p ∈ Sf, α p * Real.log p := hd
        _ ≤ |C₂ c| * ∑ p ∈ Sf, α p * Real.log p := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
        _ ≤ |C₂ c| * (|Cl| * Real.log B) := mul_le_mul_of_nonneg_left
            (h9.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)) (abs_nonneg _)
        _ = _ := by ring
    have hc1 : |coeff m ((R.tie B c).Re.PBs II)| ≤ A + |C₂ c| * |Cl| * Real.log B := by
      have := abs_sub_abs_le_abs_sub (coeff m ((R.tie B c).Re.PBs II)) (coeff m (Pfix c))
      linarith [hAle c m]
    have hA2 : A ≤ A / Real.log 2 * Real.log B := by
      calc A = A / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogB (by positivity)
    have hS : |C₂ c| * |Cl| ≤ ∑ c, |C₂ c| * |Cl| :=
      Finset.single_le_sum (f := fun c => |C₂ c| * |Cl|) (fun _ _ => by positivity) (Finset.mem_univ c)
    have hS2 := mul_le_mul_of_nonneg_right hS hlog0
    calc _ ≤ |coeff m ((R.tie B c).Re.PBs II)| := hle
      _ ≤ A + |C₂ c| * |Cl| * Real.log B := hc1
      _ ≤ _ := by rw [add_mul]; linarith
  · rw [PP_monomial_of_ne II _ m hm, abs_zero]
    exact mul_nonneg (add_nonneg (by positivity) hS0) hlog0

end GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals
