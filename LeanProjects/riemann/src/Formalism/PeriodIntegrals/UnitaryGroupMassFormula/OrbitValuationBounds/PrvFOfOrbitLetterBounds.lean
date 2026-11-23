import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.HidaSetting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.AdmissibleOfJetBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.LossLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SumWcLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SummableTruncatedGeometric

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem prvF_of_orbitLetterBounds : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : Ent D) (C6 C : ℝ),
    OrbitLetterBoundsAll C6 C → Shape D L X E → CLarge C6 C K ce → OrbitValuationBound E X K ce := by
  intro D L X K ce E C6 C hA hS hC
  intro p _ h _hcls hp u i hi r hr hk ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i r Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi r Th) D.R.k (wOrb D p i r)
    (eOrb E p u i r) (three_le_k D) (wOrb_pos hS p hi r) (eOrb_bounds hS p u hi r)
    (dl_off h u i r Th) (dl_on h u i r Th)
  refine kvalGe_mono hCor ?_
  have hg := orbit_place_term_le_sum hS K hC.dl1nn hC.dl2 h u hi hr hk Th
  have hw := sum_Wc_le hS h u hi r Th
  have hl := loss_le hS hC h hp hi r
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i r s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi r s).le
  have hc6 : C6 * (∑ s, wOrb D p i r s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i r s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i r Th).TT, ((orbLoc E p h u i r Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p r : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p r = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i r s) := rfl
  have hE : errF L K ce (i + 1) p r = Formalism.MainNotions.G.gam p * (topsOrb D p r : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i r s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show g0Pl X K p (i + 1) r + FOrb D (i + 1) p r - errF L K ce (i + 1) p r ≤
    (∑ s ∈ (orbLoc E p h u i r Th).TT, (orbLoc E p h u i r Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i r s)) - C6 * (∑ s, wOrb D p i r s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i r Th).TT, ((orbLoc E p h u i r Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end PI.OrbBoundFW
