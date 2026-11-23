import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLiftStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerFurther
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.PerPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_nat_smul_mem {N : ℕ} (X : Data E N) (v : Fin N → E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem X v

theorem perFr_natCast_smul {N : ℕ} (X : Data E N) (x : Frame X.Ψ N) (v : Fin N → E) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x ((n : E) • v) τ i = (n : ℂ) * perFr X x v τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ ((n : E) • v) = (n : ℂ) • Data.emb τ v := fun τ => funext fun a => by
    simp [Data.emb, map_natCast]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v R
  obtain ⟨n, hn, hnv⟩ := exists_nat_smul_mem (U.X k) v
  obtain ⟨C₁, B, h₁⟩ := GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
    _ hnv R
  obtain ⟨C₃, h₃⟩ : ∃ C₃ : ℝ, ∀ᶠ w in imTop, (U.X k).p0 = 0 → ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := by
    by_cases h0 : (U.X k).p0 = 0
    · obtain ⟨C₃, h⟩ := GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
        h0 v
      exact ⟨C₃, h.mono fun w hw _ => hw⟩
    · exact ⟨0, .of_forall fun w h => absurd h h0⟩
  have him : ∀ᶠ w in imTop, 1 ≤ w.im :=
    (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_ge_atTop 1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨max (C₁ / n) 0 + max C₃ 0, B, ?_⟩
  filter_upwards [h₁, h₃, him] with w hw1 hw3 hwi hR τ i
  have hpow : 1 ≤ w.im ^ B := one_le_pow₀ hwi
  have hK0 : 0 ≤ max (C₁ / n) 0 + max C₃ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hK1 : C₁ / n ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hK3 : C₃ ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hlat : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := by
    intro τ i h
    have h2 := hw1 hR τ i h
    rw [perFr_natCast_smul, norm_mul, Complex.norm_natCast] at h2
    have h3 : ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₁ / n * w.im ^ B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn']
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have hzero : 0 ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := mul_nonneg hK0 (by positivity)
  by_cases hτ : τ ∈ (U.X k).Ψ
  · by_cases hi : i < N - (U.X k).p0
    · exact hlat τ i (Or.inl ⟨hτ, hi⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dif_pos hτ, dif_neg (by omega)]
      rw [e, norm_zero]
      exact hzero
  · by_cases hc : conjEmb τ ∈ (U.X k).Ψ
    · by_cases h0 : (U.X k).p0 = 0
      · calc ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := hw3 h0 τ i hτ
          _ ≤ max (C₁ / n) 0 + max C₃ 0 := hK3
          _ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := le_mul_of_one_le_right hK0 hpow
      · by_cases hi : i < (U.X k).p0
        · exact hlat τ i (Or.inr ⟨hc, hi⟩)
        · have e : perFr (U.X k) (xx w) v τ i = perFr (U.X k) (xx w) v τ ((U.X k).p0 - 1) := by
            have e1 : (U.X k).p0 - 1 - i = (U.X k).p0 - 1 - ((U.X k).p0 - 1) := by omega
            unfold perFr
            rw [dif_neg hτ, dif_neg hτ, dif_pos hc, dif_pos hc]
            simp only [e1]
          rw [e]
          exact hlat τ _ (Or.inr ⟨hc, by omega⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dif_neg hτ, dif_neg hc]
      rw [e, norm_zero]
      exact hzero

end GlobalTheory.ShFam.PerPoly
