import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfRinv

theorem rinv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  intro l _ d d' n M τ Y Y' A Q hτ hY hYY' hdiv
  set f : Ainf l →+* WCb l := inclW l with hf
  let I : Ideal (WCb l) := Ideal.span {((l : WCb l)) ^ n}
  let π : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  let fW := (f.mapMatrix : Matrix (Fin d) (Fin d) (Ainf l) →+* Matrix (Fin d) (Fin d) (WCb l))
  let πM := (π.mapMatrix : Matrix (Fin d) (Fin d) (WCb l) →+* Matrix (Fin d) (Fin d) (WCb l ⧸ I))
  have hsm : ∀ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : R),
      (φ.mapMatrix : Matrix (Fin d) (Fin d) R →+* Matrix (Fin d) (Fin d) S) (c • 1) = φ c • 1 := by
    intro R S _ _ φ c; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  set t : WCb l := f τ ^ M with ht
  have hfτ : fW (τ ^ M • 1) = t • 1 := by rw [hsm, map_pow]

  have h1 : fW Y * fW Y' = t • 1 := by rw [← map_mul, hYY', hfτ]
  obtain ⟨u, hu⟩ := hY
  have hYw : fW Y = (u : Matrix (Fin d) (Fin d) (WCb l)) := hu.symm
  have h2 : fW Y' * fW Y = t • 1 := by
    have e : fW Y' = (↑u⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) * (fW Y * fW Y') := by
      rw [← Matrix.mul_assoc, hYw, Units.inv_mul, Matrix.one_mul]
    rw [e, h1, hYw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  set s : WCb l ⧸ I := π t with hs
  have hsu : IsUnit s := (hτ.pow M).map π
  have hmod : πM (fW Y * fW (A * Q) - t • 1) = 0 := by
    ext i j
    simp only [πM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hdiv i j))
  rw [map_sub, map_mul, hsm] at hmod
  have hYZ := sub_eq_zero.mp hmod
  have h2b : πM (fW Y') * πM (fW Y) = s • 1 := by rw [← map_mul, h2, hsm]
  have hZ : πM (fW (A * Q)) = πM (fW Y') := by
    have : s • πM (fW (A * Q)) = s • πM (fW Y') := by
      calc s • πM (fW (A * Q)) = (πM (fW Y') * πM (fW Y)) * πM (fW (A * Q)) := by
              rw [h2b, Matrix.smul_mul, Matrix.one_mul]
        _ = πM (fW Y') * (s • 1) := by rw [Matrix.mul_assoc, hYZ]
        _ = s • πM (fW Y') := by rw [Matrix.mul_smul, Matrix.mul_one]
    exact (hsu.smul_left_cancel).mp this
  have hfin : πM (fW (A * (Q * Y) - τ ^ M • 1)) = 0 := by
    rw [← Matrix.mul_assoc, map_sub, map_sub, map_mul, map_mul, hZ, h2b, hfτ, hsm, sub_self]
  intro i j
  have hij : π (f ((A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j)) = 0 := by
    have := congrFun (congrFun hfin i) j
    simpa [πM, fW, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hij)
  obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) n w (fun _ => ⟨(A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j, by rw [one_mul, ← hw, sub_self]; exact dvd_zero _⟩)
  refine ⟨a, GlobalTheory.Prism.inclW_injective ?_⟩
  rw [one_mul] at ha
  rw [map_mul, map_pow, map_natCast, ← ha]
  exact hw

end GlobalTheory.AinfRinv
