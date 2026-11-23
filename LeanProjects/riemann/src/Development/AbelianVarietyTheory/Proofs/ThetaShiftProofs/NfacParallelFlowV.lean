import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

section FlowNorm

open ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

theorem sum_step_telescope (L : ℕ → ℝ) (m : ℝ) {p r : ℕ} (hp : p ≤ r) :
    ∑ k ∈ Finset.range r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r + L 0 - 2 * L p) := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, (if p ≤ k then m else -m) * (L (k + 1) - L k) = -m * (L p - L 0) := by
    rw [← Finset.sum_range_sub L p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
  have h2 : ∑ k ∈ Finset.Ico p r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r - L p) := by
    rw [← Finset.sum_Ico_sub L hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).1]
  rw [h1, h2]; ring

theorem nfac_parallel_flowV {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) (la : Wt X.Ψ r) (m : ℝ)
    (hla : ∀ τ (j : Fin r), (la τ j : ℝ) = if X.p0 ≤ (j : ℕ) then m else -m)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) :
    X.nfac la (X.flowV e s x) * (∏ τ, (X.ttV e (X.flowV e s x) τ)⁻¹) ^ m =
      X.nfac la x * (∏ τ, (X.ttV e x τ)⁻¹) ^ m := by
  have hρ : ∀ τ, 0 < rho X e s x τ X.p0 := fun τ => rho_pos X e he hx s hT τ _ X.p0_le
  have hr : ∀ τ, rfac X la x (X.flowV e s x) τ = (rho X e s x τ X.p0)⁻¹ ^ m := by
    intro τ
    have hsg := hsg_of X hx τ
    rw [rfac_eq X e he hx s hT τ la]
    set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
    have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
    have hLr : L r = 0 := by
      simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
    have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
        ∑ k ∈ Finset.range r, (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k)) r]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hla]
      split_ifs <;> simp only [L] <;> ring
    rw [hsum, sum_step_telescope L (m / 2) X.p0_le, hL0, hLr,
      Real.rpow_def_of_pos (inv_pos.mpr (hρ τ)), Real.log_inv]
    congr 1
    simp only [L]; ring
  have hm : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (hsg_of X hx τ) (e τ) (he τ).1 (he τ).2
  have htpos : ∀ τ, 0 ≤ (X.ttV e x τ)⁻¹ := fun τ => by
    have := hm τ
    have := c_pos X τ
    rw [Data.ttV, maj_eq X hx e τ (he τ).1]
    positivity
  have ht : ∀ τ, (X.ttV e (X.flowV e s x) τ)⁻¹ = (rho X e s x τ X.p0)⁻¹ * (X.ttV e x τ)⁻¹ := by
    intro τ
    have h1 := hρ τ
    have h2 := hm τ
    have h3 := c_pos X τ
    rw [Data.ttV, Data.ttV, maj_flow X hx e τ (he τ).1 s h1.ne', maj_eq X hx e τ (he τ).1]
    simp only [rho] at h1 ⊢
    field_simp
  have hN := FlowCoefficientBounds.nfac_pos X hT la
  have hdiv := nfac_div X la x (X.flowV e s x)
  rw [div_eq_iff hN.ne', Finset.prod_congr rfl fun τ _ => hr τ,
    Real.finsetProd_rpow _ _ (fun τ _ => (inv_pos.mpr (hρ τ)).le)] at hdiv
  rw [hdiv, Finset.prod_congr rfl fun τ _ => ht τ, Finset.prod_mul_distrib,
    Real.mul_rpow (Finset.prod_nonneg fun τ _ => (inv_pos.mpr (hρ τ)).le)
      (Finset.prod_nonneg fun τ _ => htpos τ)]
  ring

end FlowNorm

theorem nfac_parallel_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (n : ℕ) (ξ' : Fin r → E), Even n → (U.X k).IsIso ξ' → ∀ x ∈ (U.X k).dom, ∀ s : (U.X k).Ψ → ℂ, (U.X k).flow ξ' s x ∈ (U.X k).dom → (U.X k).nfac (laU U 0 n k) ((U.X k).flow ξ' s x) * (∏ τ, ((U.X k).tt ξ' ((U.X k).flow ξ' s x) τ)⁻¹) ^ ((n : ℝ) / 2) = (U.X k).nfac (laU U 0 n k) x * (∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U k n ξ' hn hξ x hx s hT
  have hiso : (U.X k).IsIsoV ((U.X k).embV ξ') := fun τ =>
    ⟨by rw [show (U.X k).embV ξ' τ = Data.emb τ.1 ξ' from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  refine nfac_parallel_flowV (U.X k) ((U.X k).embV ξ') hiso (laU U 0 n k) ((n : ℝ) / 2) ?_ hx s hT
  intro τ j
  obtain ⟨m, rfl⟩ := hn
  have h2 : (m + m) / 2 = m := by omega
  simp only [laU, h2]
  split_ifs <;> simp

end GlobalTheory.ArcQ
