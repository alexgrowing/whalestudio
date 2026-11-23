import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem pointNorm_eq_norm_mul (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    X.pnorm la G z = ‖G z‖ * X.pnorm la (fun _ => (1 : ℂ)) z := by
  simp only [Data.pnorm, norm_one, one_mul]

theorem pointNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.pnorm la G z := by
  unfold Data.pnorm
  refine mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem hatNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.hatN la G z := by
  unfold Data.hatN
  refine Real.sSup_nonneg fun t ht => ?_
  obtain ⟨x', -, -, rfl⟩ := ht
  exact X.pointNorm_nonneg la G x'

theorem herm_Gm_smul_left (c : E) (x y : Fin r → E) : herm X.Gm (c • x) y = c * herm X.Gm x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Data

theorem epsilonZero_spec {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 ∧
    ∀ ε, 0 < ε → ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w →
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * ((4 * fdeg E : ℕ) : ℝ)) +
        ((4 * fdeg E : ℕ) : ℝ) + 2 <
        (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) := by
  have hf1 : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  have hd0 : 0 < dE E := field_discr_constant_pos
  have hg0 : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC0 : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  generalize hK : (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) = K2
  have hK1 : 1 ≤ K2 := by
    rw [← hK]
    have : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by positivity
    linarith
  have hN : ((4 * fdeg E : ℕ) : ℝ) = 4 * (fdeg E : ℝ) := by push_cast; ring
  generalize hR : w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * K2 * ((4 * fdeg E : ℕ) : ℝ)) +
      ((4 * fdeg E : ℕ) : ℝ) + 2 = R2
  have hR0 : 0 < R2 := by
    rw [← hR, hN]
    have : 0 ≤ 4 * (fdeg E : ℝ) * Real.log (2 * K2 * (4 * (fdeg E : ℝ))) :=
      mul_nonneg (by linarith) (Real.log_nonneg (by nlinarith))
    linarith
  generalize hB : (X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 = B
  have hB0 : 0 < B := by rw [← hB]; positivity
  have heq : flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w = min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) := by
    rw [← hB, ← hR, ← hK, hN]
    simp only [flowEpsilonBound]
    rw [← rootDiscriminant_eq_rpow]
  rw [heq]
  refine ⟨lt_min one_pos (div_pos (by positivity) (mul_pos hB0 hR0)), min_le_left _ _, fun ε hε hεlt => ?_⟩
  have hle : min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) ≤ (fdeg E : ℝ) ^ 2 / (B * R2) := min_le_right _ _
  have h1 := (le_div_iff₀ (mul_pos hB0 hR0)).1 (le_of_lt (lt_of_lt_of_le hεlt hle))
  rw [lt_div_iff₀ (mul_pos hB0 hε)]
  have hε' : ε * (B * R2) < (fdeg E : ℝ) ^ 2 := by
    have h2 := (lt_div_iff₀ (mul_pos hB0 hR0)).1 (lt_of_lt_of_le hεlt hle)
    exact h2
  calc R2 * (B * ε) = ε * (B * R2) := by ring
    _ < (fdeg E : ℝ) ^ 2 := hε'

set_option maxHeartbeats 1000000 in
theorem unipotent_vector_eq_smul_component {r : ℕ} (X : DataX E r) (z0 : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) (K : ℂ)
    (a : X.Ψ → Fin 2 → ℂ) (ha : a τ = ![-(K * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K / (X.NC : ℂ)]) :
    X.uvec ![ξ, (X.NC : E) • x] a τ = K • X.ucomp z0 ξ (X.embV x) τ := by
  have hNCc : (X.NC : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  rw [X.toData.orthogonal_component_apply]
  funext j
  simp only [Data.uvec, ha, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Data.emb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_natCast]
  generalize X.Hf z0 τ (fun a => τ.1 (x a)) (fun a => τ.1 (ξ a)) /
    X.Hf z0 τ (fun a => τ.1 (ξ a)) (fun a => τ.1 (ξ a)) = q
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem short_vector_setting_exists {r : ℕ} (X : DataX E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {ξ : Fin r → E}
    {ν : X.Ψ → ℝ} {c1 w : ℝ} {z0 : Frame X.Ψ r} (hH : ShortVectorHypotheses X la P ξ ν c1 w z0) {x : Fin r → E}
    (hxL : x ∈ X.L') (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    ∃ a, IsotropicFlowSetting X la P ξ ν c1 w z0 x a := by
  have hξ0 : ξ ≠ 0 := hH.2.2.1.2.2
  have hune : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0 := X.toData.orthogonal_component_ne_zero z0 hξ0 hxE
  obtain ⟨K, hK⟩ : ∃ K : X.Ψ → ℂ, ∀ τ,
      K τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨fun τ => ![-(K τ * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K τ / (X.NC : ℂ)],
    hH, hxL, hxξ, hxx, hxE, hune, fun τ => ?_⟩
  rw [← hK τ]
  exact unipotent_vector_eq_smul_component X z0 ξ x τ (K τ) _ rfl

theorem isotropic_pair_in_lattice {r : ℕ} (X : DataX E r) {ξ x : Fin r → E} (hiso : X.IsIso ξ) (hxL : x ∈ X.L')
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] ∧ ∀ i, ![ξ, (X.NC : E) • x] i ∈ X.Λ := by
  have hξ0 : ξ ≠ 0 := hiso.2.2
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ, HermitianTraceFormVanishing.cc_zero]
  refine ⟨⟨fun i k => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases k <;>
      simp [hiso.2.1, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hxξ, hξx, hxx]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNCE : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
      have htN : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNCE
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]; exact eq_neg_of_add_eq_zero_right hst
      apply hxE (-(s / (t * (X.NC : E))))
      calc x = (t * (X.NC : E))⁻¹ • ((t * (X.NC : E)) • x) := by
            rw [smul_smul, inv_mul_cancel₀ htN, one_smul]
        _ = -(s / (t * (X.NC : E))) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · fin_cases i
    · exact hiso.1
    · exact X.NC_sub x hxL

end

end ReciprocityTheory.ChartRestriction.G.FD
