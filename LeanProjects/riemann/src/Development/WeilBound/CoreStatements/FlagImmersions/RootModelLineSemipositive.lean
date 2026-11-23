import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_nonvanishing_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smooth_metric_zpow {A : HermLine ι} (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hA.pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    exact (hA.pow (m + 1)).inv fun z hz => pow_ne_zero _ (A.pos z hz).ne'

theorem combLine_smooth {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  exact contDiffOn_prod fun j _ => smooth_metric_zpow (h j) (n j)

theorem combLine_conj_invariant {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsConjInvariantH (ℓ j)) : IsConjInvariantH (combLine ℓ n) := by
  intro z
  show ∏ j, (ℓ j).h _ ^ n j = ∏ j, (ℓ j).h z ^ n j
  exact Finset.prod_congr rfl fun j _ => by rw [h j z]

end

theorem leviForm_congr_eventually {ι : Type} [Fintype ι] {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : ι → ℂ) : leviForm φ z w = leviForm ψ z w := by
  simp only [leviForm, h.fderiv.fderiv_eq]

theorem leviForm_smul {ι : Type} [Fintype ι] (c : ℝ) (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) :
    leviForm (c • φ) z w = c * leviForm φ z w := by
  by_cases hc : c = 0
  · subst hc
    simp [leviForm]
  · letI : Invertible c := invertibleOfNonzero hc
    have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ :=
      funext fun x => fderiv_const_smul_of_invertible c
    have h2 : fderiv ℝ (c • fderiv ℝ φ) z = c • fderiv ℝ (fderiv ℝ φ) z :=
      fderiv_const_smul_of_invertible c
    simp only [leviForm, h1, h2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem root_model_line_semipositive : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  intro Ψ _ N M t lam s q n hn hS
  have hsm : IsSmoothHerm (combLine (M.line t) n) := by
    refine combLine_smooth _ _ fun j => ?_
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hcj : IsConjInvariantH (combLine (M.line t) n) := by
    refine combLine_conj_invariant _ _ fun j => ?_
    cases j with
    | none => exact M.A_conj
    | some r => exact M.x_conj t r
  refine ⟨⟨hsm, fun z hz w hw => ?_⟩, hcj⟩
  have hev : (fun y => Real.log ((combLine (M.line t) n).h y)) =ᶠ[𝓝 z]
      ((q : ℝ) • M.weight t lam s) := by
    filter_upwards [isOpen_nonvanishing_blocks.mem_nhds hz.1] with y hy
    rw [Pi.smul_apply, smul_eq_mul]
    show Real.log (∏ j, (M.line t j).h y ^ n j) =
      (q : ℝ) * ∑ j, M.coef lam s j * Real.log ((M.line t j).h y)
    rw [Real.log_prod (fun j _ => zpow_ne_zero _ ((M.line t j).pos y hy).ne'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.log_zpow, hn j]
    ring
  rw [leviForm_congr_eventually hev w, leviForm_smul]
  exact mul_nonneg (Nat.cast_nonneg _) (hS z hz w hw)

end RootFieldNumerics
