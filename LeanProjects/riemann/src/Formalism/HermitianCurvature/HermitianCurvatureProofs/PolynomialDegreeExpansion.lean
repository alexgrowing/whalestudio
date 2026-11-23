import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeActionExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordMonicExtraction

namespace Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.RealWeightedForms
open scoped Matrix

theorem first_polynomial_expansion_formula : PositionExpansionTopCoefficients := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x Ξ y hData hΞ
  obtain ⟨-, -, -, -, hinj, hnew, -, -, -, -, hx⟩ := hData
  have h := Formalism.FourierDecayAlt.P.FreeActionExpansion.expand ρ QQ f s w vA vB vAv vBv x Ξ hΞ hx (Lp sl y) ?_ ?_ ?_ 1 1
  · simp only [one_smul] at h
    unfold WK
    rw [h]
    congr 1
    simp [Lp, List.map_ofFn, Function.comp_def]
  · intro l hl
    simp only [Lp, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    simp
  · simp only [Lp, List.map_ofFn]
    exact List.nodup_ofFn.mpr hinj
  · intro l hl
    simp only [Lp, List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    exact hnew a

theorem first_polynomial_degree : GridDegreeIdentity := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x grid hData hinj
  obtain ⟨-, -, -, -, -, -, -, hsh1, hsh2, -, -⟩ := id hData
  have h := Formalism.FourierDecayAlt.P.plane_wave_word_formula A (Ix S → V) (frmS ρ (RRw QQ w * Vw f s w)) n K
    (fun _ => ⟨vA, vB, vAv, vBv, s⟩) grid x x (fun _ => ⟨hsh1, hsh2⟩) hinj
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, frmS_apply] at h
  have he : frm ρ (RRw QQ w * Vw f s w) x x = frm ρ (RRw QQ w) (act (Vw f s w) x) x := by
    simp only [frm, act_mul]
  rw [← he, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (first_polynomial_expansion_formula A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x (frmS ρ (RRw QQ w * Vw f s w))
    (fun a => grid a (j a)) hData (fun _ _ => rfl)).symm

theorem u72 : CombinedDegreeSizeBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid hData hG0 hImp
    hinj hadm
  have hdeg := first_polynomial_degree A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x grid hData hinj
  calc ‖s‖ ^ K * ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖
      = ‖s ^ K * frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ := by rw [norm_mul, norm_pow]
    _ = ‖∑ j : Fin K → Fin (2 * n + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) *
          WK ρ QQ f s w vA vB vAv vBv sl (fun a => grid a (j a)) x‖ := by rw [hdeg]
    _ ≤ ∑ j : Fin K → Fin (2 * n + 1), ‖((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) *
          WK ρ QQ f s w vA vB vAv vBv sl (fun a => grid a (j a)) x‖ := norm_sum_le _ _
    _ ≤ _ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun a _ => abs_nonneg _)
      have h := Real.abs_le_sqrt (first_polynomial_size A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β
        (fun a => grid a (j a)) hData hG0 hImp (hadm j).1 (hadm j).2)
      rwa [abs_norm] at h

theorem first_polynomial_degree_of_parts : DegreeIdentityOfParts := fun _ _ _ => first_polynomial_degree

theorem unipotent_degree_of_parts : CombinedBoundOfDegreeSize := fun _ _ => u72

end Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion

theorem Formalism.FourierDecayAlt.P.first_polynomial_expansion_identity : Formalism.FourierDecayAlt.FormPairingAction.PositionExpansionTopCoefficients := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_expansion_formula
theorem Formalism.FourierDecayAlt.P.first_polynomial_degree_identity : Formalism.FourierDecayAlt.FormPairingAction.GridDegreeIdentity := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_degree
theorem Formalism.FourierDecayAlt.P.unipotent_degree_bound : Formalism.FourierDecayAlt.FormPairingAction.CombinedDegreeSizeBound := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.u72
theorem Formalism.FourierDecayAlt.P.first_polynomial_degree_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.DegreeIdentityOfParts := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.first_polynomial_degree_of_parts
theorem Formalism.FourierDecayAlt.P.unipotent_degree_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.CombinedBoundOfDegreeSize := Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion.unipotent_degree_of_parts
