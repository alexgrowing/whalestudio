import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def KronHolStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have h1 := h γ hγ
  rw [h0, zero_pow hn.ne'] at h1
  exact zero_ne_one h1

theorem poin_single {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    {γ0 : GL (Fin r) E} (h0 : γ0 ∈ X.Γ) (hz : ∀ γ ∈ X.Γ, γ ≠ γ0 → P (lact γ x) = 0) :
    poin X la P x = (X.χ la γ0)⁻¹ * P (lact γ0 x) := by
  unfold poin
  rw [tsum_eq_single ⟨γ0, h0⟩ fun γ hγ => by
    rw [hz γ.1 γ.2 fun h => hγ (Subtype.ext h), mul_zero]]

theorem poin_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hz : ∀ γ ∈ X.Γ, P (lact γ x) = 0) : poin X la P x = 0 := by
  unfold poin
  exact (tsum_congr fun γ => by rw [hz γ.1 γ.2, mul_zero]).trans tsum_zero

theorem leviO_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (fun _ => (0 : ℝ)) z ξ = 0 := by
  have h0 : ∀ k, wdb (nd X) k (fun _ : V (nd X) => (0 : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviO, leviM, leviV, wd, h0]

theorem kronHol_of_psi (hK : KronHolPsiStatement (E := E)) : KronHolStatement (E := E) := by
  intro r X Xa Fl hPD hm hL j
  obtain ⟨bb, m, hb1, hb2, hb3⟩ := hm

  obtain ⟨η, hη, hpos⟩ := Xa.posF
  have hmarg : ∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨bb, m, hb1, hb2, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      exact hb3 x0 hx z hz ξ⟩
  have heta : ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 (fun _ => (0 : ℝ)) z ξ :=
    ⟨η, hη, fun x0 hx z hz ξ => by
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.leviO_zero, add_zero]
      have h1 := hpos 0 le_rfl (by rw [zero_mul]; positivity) x0
        (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x0 hx) z hz ξ
      rw [zero_mul, zero_mul, sub_zero, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.leviM_comb X x0 hx hz] at h1
      exact h1⟩
  obtain ⟨x0, W, bb', F, P, γ0, h1, h2, h3, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hK r X Xa Fl hPD (fun _ => 0) (fun _ _ _ _ _ _ => rfl) (fun _ _ => contDiffOn_const)
      ⟨0, fun _ _ => le_rfl⟩ hmarg heta hL j
  exact ⟨x0, W, bb', F, P, γ0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem interp_of (hP : PoinStatement (E := E)) (hK' : KronHolPsiStatement (E := E)) :
    InterpStatement (E := E) := by
  intro r X Xa Fl hPD hm hL hSS
  have hK := ReciprocityTheory.ChartRestriction.G.AR.Up.kronHol_of_psi hK'
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.interp_of_kron X Xa.Fp Fl.xs fun j => ?_
  obtain ⟨x0, W, bb, F, P, γ0, hO, hW, hWL, hbb, hF, hIn, hBE, hPF, hγ0, hne, hzero⟩ :=
    hK r X Xa Fl hPD hm hL j

  have hIn' : InAt X x0 W bb (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z) := by
    unfold InAt at hIn ⊢
    have h1 : ∀ z, ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z‖ ^ 2 / kaF X x0 bb z) *
        W (cpt X x0 z) = ENNReal.ofReal (‖X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j))‖ ^ 2) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := fun z => by
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIn
  have hBE' : IsBEq X Xa.Fp (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x) :=
    ⟨(differentiableOn_const _).mul hBE.1, fun x hx b hb => by dsimp only; rw [hBE.2 x hx b hb]; ring⟩
  obtain ⟨-, hbdd, -⟩ := hP r X x0 hO hPD Xa.Fp W bb hW hWL hbb
    (fun z => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * F z)
    (fun x => X.χ Xa.Fp γ0 / P (lact γ0 (Fl.xs j)) * P x)
    ((differentiableOn_const _).mul hF) hIn' hBE' fun z hz => by simp only [hPF z hz]
  refine ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ss_sub_ssgt0 X Xa.Fp (hSS _ hbdd), fun j' => ?_⟩
  split_ifs with hj
  · subst hj
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.poin_single X Xa.Fp _ (Fl.xs j') hγ0 fun γ hγ hγ' => by
      simp only [hzero γ hγ j' (Or.inl hγ'), mul_zero]]
    rw [div_mul_cancel₀ _ hne, inv_mul_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.chi_ne_zero X Xa.Fp hγ0)]
  · exact ReciprocityTheory.ChartRestriction.G.AR.Up.poin_zero X Xa.Fp _ (Fl.xs j') fun γ hγ => by
      simp only [hzero γ hγ j' (Or.inr hj), mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
