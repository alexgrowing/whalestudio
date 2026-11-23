import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ProductFormIsSectionPointwiseNormLeStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CuspAndSupCLeOfBounded
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsSmallCoeffRuleNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EqZeroOfMulEqZeroOfReadingNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NonemptyComponentComplexUniformisationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem phiFD_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r) (t : ℝ)
    (x : FD.Frame X.Ψ r) : 0 ≤ I2.phiFD X t x := by
  unfold I2.phiFD
  split_ifs
  · positivity
  · exact le_rfl

theorem exists_etaRule_cusp_ne_zero_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ₀ : c.F →+* ℂ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodEmb c σ₀ → AllTest Xo c → 2 ≤ r → ∀ (R : ℕ), Odd R → 1 < R → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (i : ℕ) (J : Type) (_ : Fintype J) (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Spans xs ∧ IsEtaRule Xo c R cf xs f ∧ f ∈ cusp Xo c U 0 (2 * R ^ 4 * r * i) ∧ f ≠ 0 ∧ (∀ k, ∃ x ∈ ((U σ₀).X k).dom, rdU (U σ₀) f k x ≠ 0) ∧ (∀ a n g, Dom a n → g ∈ sec Xo c a n → f * g = 0 → g = 0) ∧ (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 (2 * R ^ 4 * r * i) k) (rdU (U σ) f k) x ≤ Real.exp (-(i : ℝ) * (I2.phiFD ((U σ).X k) (I2.th (E := E) q R0) x - p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))))) ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 (2 * R ^ 4 * r * i) f ≤ Real.exp (i * p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))) := by
  intro E _ _ _ H Dw l Xo c r U σ₀ hU hσ₀ hT hr R hR hR1 DF q m R0 hrun hm
  obtain ⟨i, inst, x₀, cf, f, hi, hG, hJ, hcf, hsp, hf, hnz⟩ :=
    GlobalTheory.EtaAn.exists_small_coeff_rule_ne_zero E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) hT R hR hR1 hr
  have hn : r * (2 * R ^ 4 * i) = 2 * R ^ 4 * r * i := by ring
  have hRp : 0 < R := by omega
  have hsec : f ∈ sec Xo c 0 (2 * R ^ 4 * r * i) := by
    rw [← hn, ← hG]
    exact (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR _ r cf _).2 f hf
  have hev : Even (2 * R ^ 4 * r * i) := ⟨R ^ 4 * r * i, by ring⟩
  have h2 : 2 ≤ 2 * R ^ 4 * r * i := by
    have h1 : 0 < R ^ 4 * r * i := by positivity
    have h3 : 2 * R ^ 4 * r * i = 2 * (R ^ 4 * r * i) := by ring
    omega
  have hN : 1 ≤ max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2) :=
    Nat.mul_pos (lt_of_lt_of_le Nat.one_pos (le_max_left _ _)) (pow_pos hRp _)
  have harch : ∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom,
      ((U σ).X k).pnorm (laU (U σ) 0 (2 * R ^ 4 * r * i) k) (rdU (U σ) f k) x ≤
        Real.exp (-(i : ℝ) * (I2.phiFD ((U σ).X k) (I2.th (E := E) q R0) x -
          p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2)))) := by
    intro σ hσ
    rw [← hn]
    exact (GlobalTheory.T.productForm_isSection_pointwiseNorm_le E H Dw l Xo c σ r (U σ) hσ (hU σ hσ) hT R i _ hR hR1 hG hN _ cf _ f hJ hcf hsp hf
      DF q m R0 hrun hm).2
  have hcusp := GlobalTheory.cusp_and_supC_le_of_bounded E H Dw l Xo c r U (2 * R ^ 4 * r * i) f
    (Real.exp (i * p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2)))) h2 hev hU hsec
    (fun σ hσ k x hx => (harch σ hσ k x hx).trans (Real.exp_le_exp.2 (by
      have h0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (phiFD_nonneg ((U σ).X k) (I2.th (E := E) q R0) x)
      linarith))) (Real.exp_pos _).le
  refine ⟨i, _, inferInstance, cf, _, f, hi, hG, hsp, hf, hcusp.1, ?_, hnz, ?_, harch, hcusp.2⟩
  · rintro rfl
    obtain ⟨k⟩ := GlobalTheory.T.nonempty_component_complexUniformisation E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) (by omega)
    obtain ⟨x, -, hx⟩ := hnz k
    apply hx
    rw [map_zero]
    rfl
  · intro a n g hD hg hfg
    exact GlobalTheory.eq_zero_of_mul_eq_zero_of_reading_ne_zero E H Dw l Xo c σ₀ r (U σ₀) hσ₀ (hU σ₀ hσ₀) 0 a _ n f g
      ⟨fun _ => antitone_const, hev⟩ hD hsec hg hnz hfg

end GlobalTheory.EtaAn
