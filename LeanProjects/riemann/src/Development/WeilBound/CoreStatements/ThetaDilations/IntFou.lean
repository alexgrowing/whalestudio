import Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem int_fou {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
    (h : NADual V χ μ) {f : V → ℂ} (hf : SB f) : ∫ y, fou χ μ f y ∂μ = f 0 := by
  have := (fou_sb h hf).2 0
  simpa only [fou, neg_zero, chi_sym h _ 0, chi_zero h, mul_one] using this

theorem recip : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F, b ≠ 0 → cG B ρ P τ * eiTerm ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) b = eiTerm ψ lf B ρ P φ τ (-b⁻¹) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ φ hφ τ hτ b hb
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hD := H.2.2.2.2.2
  set m : ℝ := |((Algebra.norm ℚ (b⁻¹ : F) : ℚ) : ℝ)|⁻¹ ^ M with hm
  have hm0 : 0 < m := pow_pos (inv_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 (inv_ne_zero hb)))) M
  obtain ⟨γ, -, hγ⟩ := weil_id H (uA (Units.mk0 b hb)) hm0 (mod_rat hlf h1 hQ.2.1 B (Units.mk0 b hb)⁻¹)
  set c : A F := algebraMap F (A F) b⁻¹ with hc
  have hγ' : ∀ φ, SB φ → opU ψ (hf F) (Bf B) (algebraMap F (A F) b) (fou (chiB ψ (Bf B)) (muF B lf) φ) =
      (γ * m) • fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹))
        (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ)))) := by
    intro φ hφ
    refine (hγ φ hφ).trans ?_
    rw [mul_smul, ← fou_smul (m : ℂ), map_neg]
    congr 2
    funext u
    simp only [opU, opD, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, mul_left_comm (m : ℂ)]
    rfl
  have hO : IsOrth B ρ 1 fun _ => 1 := ⟨by simp, fun _ => by simp⟩
  have hU := fun φ τ => (GlobalTheory.T.theta_function_modularity F ψ hψ ι M B ρ P hQ _ _ hO φ τ)
  have hW := GlobalTheory.T.theta_function_automorphy F lf hlf h1 ψ hψ ι M B ρ P hQ _ _ hO
  have hG := GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ
  obtain ⟨φ₀, hφ₀, hne⟩ := (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ _ _ hO τ hτ).2
  have hρ : ∀ w, ((ρ w b : ℝ) : ℂ) ≠ 0 := fun w => by exact_mod_cast (map_ne_zero (ρ w)).2 hb
  have him : ∀ {σ : InfinitePlace F → ℂ}, (∀ w, 0 < (σ w).im) → ∀ w, 0 < (-(σ w)⁻¹).im := fun h w => by
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos (h w) (Complex.normSq_pos.2 fun h0 => by simpa [h0] using h w)
  set τ₁ : InfinitePlace F → ℂ := fun w => τ w + (ρ w (-b⁻¹) : ℝ) with hτ₁
  have p1 : ∀ w, 0 < (τ₁ w).im := fun w => by simpa [hτ₁] using hτ w
  set τ₄ : InfinitePlace F → ℂ := fun w => ((ρ w b⁻¹ : ℝ) : ℂ) ^ 2 * -(τ₁ w)⁻¹ + (ρ w (-b⁻¹) : ℝ) with hτ₄
  have p4 : ∀ w, 0 < (τ₄ w).im := fun w => by
    simp only [hτ₄, Complex.add_im, Complex.ofReal_im, add_zero, ← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero ((map_ne_zero (ρ w)).2 (inv_ne_zero hb))) (him p1 w)
  have e4 : (fun w => -(τ₄ w)⁻¹) = fun w => -(τ w)⁻¹ + (ρ w b : ℝ) := by
    funext w
    have h0 : τ w ≠ 0 := fun h => by simpa [h] using hτ w
    have h2 : τ₁ w ≠ 0 := fun h => by simpa [h] using p1 w
    have h3 : τ w * (ρ w b : ℝ) - 1 ≠ 0 := fun h => h2 (by
      simp only [hτ₁, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
      field_simp [hρ w]
      linear_combination h)
    have h5 : τ₄ w = -(τ w / (τ w * (ρ w b : ℝ) - 1)) := by
      have h6 : τ₁ w = (τ w * (ρ w b : ℝ) - 1) / (ρ w b : ℝ) := by
        simp only [hτ₁, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
        field_simp [hρ w]
        ring
      have h7 := hρ w
      simp only [hτ₄, h6, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
      generalize ((ρ w b : ℝ) : ℂ) = r at h3 h7 ⊢
      rw [inv_div, div_eq_mul_inv, div_eq_mul_inv]
      have h8 := mul_inv_cancel₀ h3
      have h9 := mul_inv_cancel₀ h7
      linear_combination (-(r⁻¹ * (τ w * r - 1)⁻¹) - τ w * (τ w * r - 1)⁻¹) * h9 + r⁻¹ * h8
    rw [h5]
    field_simp
    ring
  have s1 := sb_opU H (algebraMap F (A F) (-b⁻¹)) hφ₀
  have s3 : SB (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ₀))) :=
    sb_opD H 1 (uA (Units.mk0 b hb)⁻¹) (fou_sb hD s1).1
  have t1 := (hW _ s1 τ₁ p1).trans ((hU φ₀ τ).1 (-b⁻¹))
  have t4 := (hW _ (sb_opU H (algebraMap F (A F) (-b⁻¹)) s3) τ₄ p4).trans
    (((hU _ _).1 (-b⁻¹)).trans ((hU _ fun w => -(τ₁ w)⁻¹).2.1 b⁻¹ (inv_ne_zero hb)))
  have t0 := hW φ₀ hφ₀ τ hτ
  rw [← (hU _ fun w => -(τ w)⁻¹).1 b, hγ' φ₀ hφ₀, (hU _ _).2.2, ← e4] at t0
  have t5 := (hG τ₄ p4).2.2.1
  have key : cG B ρ P τ * (γ * m) * cG B ρ P (fun w => -(τ₄ w)⁻¹) = cG B ρ P τ₁ := by
    refine mul_right_cancel₀ hne ?_
    conv_rhs => rw [← t0]
    conv_lhs => rw [← t1, ← t4]
    linear_combination (cG B ρ P τ * (γ * m) * cG B ρ P τ₁ * theta B ρ P 1 (fun _ => 1)
      (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) (opD 1 c
        (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ₀)))))
      fun w => -(τ₄ w)⁻¹) * t5
  have s1' := sb_opU H (algebraMap F (A F) (-b⁻¹)) hφ
  have s3' : SB (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ))) :=
    sb_opD H 1 (uA (Units.mk0 b hb)⁻¹) (fou_sb hD s1').1
  have f1 : fstar ψ (hf F) (Bf B) (muF B lf) (fou (chiB ψ (Bf B)) (muF B lf) φ) (algebraMap F (A F) b) =
      γ * m * fstar ψ (hf F) (Bf B) (muF B lf) φ (algebraMap F (A F) (-b⁻¹)) := by
    rw [fstar, hγ' φ hφ]
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, int_fou hD (sb_opU H _ s3')]
    simp [opU, opD, qf, fou, chiB, fstar]
  rw [eiTerm, eiTerm, f1, ← e4, ← key]
  ring

end PositivityTheory.PlacePermOperatorBicommutantSpan
