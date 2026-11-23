import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (ℓ : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (ℓ.h (fun p => c p.1 * z p)) = Real.log (ℓ.h z) + ∑ k, (ℓ.a k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [ℓ.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hn k)) (ℓ.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  simp only [Real.log_zpow]

theorem coef_add_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : R.coef (lam - s • nu) s j + s * R.coef nu (-1) j = R.coef lam 0 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, R.x_deg]

theorem torus_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' n₀ q₀ s t cc z v hq hn' hn₀ hc hz hv
  have hq0 : (q₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hn : ∀ k, ‖cc k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  have hzc : ∀ k, ∃ i, (fun p : (Σ k, RM.ι k) => cc p.1 * z p) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

  have ha : ∀ k, (((combLine (RM.line 1) n₀).a k : ℤ) : ℝ) = ∑ j, (n₀ j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
    intro k
    simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl

  have h1 : Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ =
      Real.log ‖v‖ + ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr hv)
      (Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k))),
      Real.log_prod (fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k)))]
    simp only [norm_zpow, Real.log_zpow]

  have h2 : RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) =
      RM.weight t (lam - s • nu) s z +
        ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ := by
    simp only [RootModel.weight, log_h_scale _ cc z hc hz, line_a RM t, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hlog : ∀ w : (Σ k, RM.ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      Real.log (∏ r, (Or.sing r).h w ^ n' (some r)) = ∑ r, (n' (some r) : ℝ) * Real.log ((Or.sing r).h w) := by
    intro w hw
    rw [Real.log_prod (fun r _ => (zpow_pos ((Or.sing r).pos w hw) _).ne')]
    simp only [Real.log_zpow]
  have h3 : Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) =
      Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) +
        ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [hlog _ hzc, hlog z hz]
    simp only [log_h_scale _ cc z hc hz, Or.sing_deg, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hn'none : (n' none : ℝ) = 0 := by
    rw [hn' none]
    simp [RootModel.coef]
  have h4 : ∀ k, s / q₀ * ((combLine (RM.line 1) n₀).a k : ℝ) +
      ∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ) =
      ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) := by
    intro k
    have e1 : ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) = ∑ j, (n' j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
      rw [Fintype.sum_option, hn'none, zero_mul, zero_add]
      exact Finset.sum_congr rfl fun r _ => by simp only [RootModel.line, RM.x_deg]
    rw [e1, ha, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hn₀ j, hn' j, ← coef_add_smul RM lam nu s j]
    field_simp
    ring
  rw [h1, h2, h3]
  have h5 : s / q₀ * ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ +
      ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ =
      ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h4 k]
    ring
  linear_combination h5

end GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit
