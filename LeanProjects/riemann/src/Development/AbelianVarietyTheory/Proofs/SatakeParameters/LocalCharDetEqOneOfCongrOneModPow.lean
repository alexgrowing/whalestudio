import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.AwayMat

theorem muAt_det_congr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 _hX _hPr _hsel hL i P n k hk
  have hD : 1 ≤ cst.D P := hL.cst_ok.D_pos P
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  set Z : Fin n → Fin n → X.E := fun a b => (qOf P.1 : X.E) ^ (cst.D P - 1) *
    (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single b (1 : X.E)) a - (Pi.single b (1 : X.E) : Sp X.E n) a)) with hZ
  set A : Fin n → Fin n → X.E := fun a b => (Pi.single b (1 : X.E) : Sp X.E n) a with hA
  have hZi : ∀ a b, IntAt P.1 (Z a b) := fun a b => (intAt_pow (intAt_nat _) _).mul (hk b a)
  have hAi : ∀ a b, IntAt P.1 (A a b) := fun a b => by
    simp only [hA, Pi.single_apply]
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hpow : (qOf P.1 : X.E) * (qOf P.1 : X.E) ^ (cst.D P - 1) = (qOf P.1 : X.E) ^ cst.D P := by
    rw [← pow_succ']
    congr 1
    omega
  have hM : LinearMap.toMatrix (Pi.basisFun X.E (Fin n)) (Pi.basisFun X.E (Fin n)) k.toLinearMap =
      Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b := by
    ext a b
    rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, Matrix.of_apply, hZ, hA]
    simp only
    rw [← mul_assoc, hpow, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
    simp
  have hdet : ((LinearEquiv.det k : X.Eˣ) : X.E) = Matrix.det (Matrix.of fun a b => A a b + (qOf P.1 : X.E) * Z a b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Pi.basisFun X.E (Fin n)), hM]
  have hA1 : (Matrix.of fun a b => A a b) = 1 := by
    ext a b
    simp [hA, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hred : redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E) = redP P.1 (1 : X.E) := by
    rw [hdet, LastSteps.redP_det_add_q hAi hZi, hA1, Matrix.det_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by
    rw [reduction_one₂]
    exact isUnit_one
  have hu : IsUnit (redP P.1 ((LinearEquiv.det k : X.Eˣ) : X.E)) := hred ▸ h1
  unfold muAt
  rw [LastSteps.locChar_unit _ _ hu, LastSteps.unitV_congr _ hred]
  unfold LocE.unitV
  rw [dif_pos h1, show h1.unit = 1 from Units.ext reduction_one₂, map_one, Units.val_one]

end GlobalTheory.AwayMat
