import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSmallCoeffEtaValAtNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem nonzeroRule_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem exists_small_coeff_rule_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R : ℕ), Odd R → 1 < R → 2 ≤ r → ∃ (i : ℕ) (_ : Fintype (LatMod Dw R)) (x₀ : Fin r → Dw.La) (cf : (Fin r → LatMod Dw R) → ℤ) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Fintype.card (Fin r → LatMod Dw R) ≤ R ^ (2 * I2.PT.f E * r ^ 2) ∧ (∀ j, |cf j| ≤ (max 1 (Fintype.card U.Comp) * R ^ (8 * I2.PT.f E * r ^ 2) : ℕ)) ∧ Spans (shiftFam R x₀ : (Fin r → LatMod Dw R) → Fin r → LatMod Dw (R ^ 4)) ∧ IsEtaRule Xo c R cf (shiftFam R x₀) f ∧ ∀ k, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU hT R hR h1 h2
  have hr : r = Dw.p + Dw.q := hU.1
  subst hr
  obtain ⟨hfG, hfL, hcL, hcG, hdiv, ⟨x₀, hx₀⟩, hspan⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1
  obtain ⟨i, hi⟩ := hdiv hR h2
  letI hFin : Fintype (LatMod Dw R) := Fintype.ofFinite _
  have hf : FD.fdeg E = I2.PT.f E := rfl
  rw [hf] at hcL hcG
  choose xk hxk using fun k => nonzeroRule_dom_nonempty (U.X k)
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  let e := Fintype.equivFin U.Comp
  obtain ⟨cf, hcf, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR h1
    (Dw.p + Dw.q) x₀ (CAt σ) (Fintype.card U.Comp) (fun a => U.un (e.symm a) ⟨xk _, hxk _⟩)
  obtain ⟨f, hrule, -⟩ := (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR
    (Fin (Dw.p + Dw.q) → LatMod Dw R) (Dw.p + Dw.q) (fun j => (cf j : ℤ)) (shiftFam R x₀)).1
  refine ⟨i, hFin, x₀, fun j => (cf j : ℤ), f, ?_, hi, ?_, ?_, ?_, hrule, ?_⟩
  · have hpos : 0 < Nat.card (LevGrp Dw (R ^ 4)) := Nat.card_pos
    rw [hi] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  · rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcL, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  · intro j
    rw [Nat.abs_cast]
    exact_mod_cast (hcf j).trans (Nat.mul_le_mul (le_max_right _ _) hcG)
  · intro j
    exact hspan _ x₀ hx₀ j (LinearEquiv.refl _ _)
  · intro k
    obtain ⟨a, rfl⟩ := e.symm.surjective k
    refine ⟨xk _, hxk _, ?_⟩
    have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR _ _ _ _ f hrule (CAt σ) (U.un (e.symm a) ⟨xk _, hxk _⟩)
      (hT _ _)).1
    have h0 := hne a _ hv
    have e1 : rdU U f (e.symm a) (xk _) = toC (evR Xo c f (U.un (e.symm a) ⟨xk _, hxk _⟩)) := dif_pos (hxk _)
    rw [e1]
    exact h0

end GlobalTheory.EtaAn
