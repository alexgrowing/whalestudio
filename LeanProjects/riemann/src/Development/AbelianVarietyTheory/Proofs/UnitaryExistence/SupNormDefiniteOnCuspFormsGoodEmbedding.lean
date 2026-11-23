import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjectiveStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem SupNormCusp.eq_zero_of_pnorm_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (h : X.pnorm la P x = 0) : P x = 0 := by
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx' τ).2 i
    rw [h0] at this
    simp at this
  unfold Data.pnorm at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact norm_eq_zero.1 h1
  · exfalso
    refine (ne_of_gt ?_) h1
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))

theorem supNorm_definite_on_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  intro E _ _ _ H Dw l Xo c r U hU a n hd σ hσ f hf h0
  refine (GlobalTheory.T.rdU_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c σ r (U σ) (hU σ hσ) a n).2 f
    (Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf) fun k x hx => ?_
  have hfin := Formalism.L2.PjFree.supE_cusp_ne_top hσ hf
  have hE : Formalism.L2.PjFree.supE (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) f) = 0 := by
    unfold Formalism.L2.PjFree.supN at h0
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hfin
  have hle : ENNReal.ofReal (((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k)
      (Formalism.L2.PjFree.rdU (U σ) f k) x) ≤ 0 := by
    rw [← hE]
    exact le_iSup (fun p : Formalism.L2.PjFree.FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm
      (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
  have hp : ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x = 0 := by
    refine le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hle zero_le)) ?_
    unfold Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)
  exact SupNormCusp.eq_zero_of_pnorm_eq_zero _ _ _ x hx hp

end GlobalTheory
