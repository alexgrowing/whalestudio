import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLawStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem collect_factors {ι : Type} (s : Finset ι) (A B p q : ι → ℂˣ) (u v : ℂ)
    (h : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) * u =
      ((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) :
    u = ((∏ i ∈ s, (A i * (B i)⁻¹ * (p i * (q i)⁻¹)) : ℂˣ) : ℂ) * v := by

  have hne : (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))
  have hu : u = (∏ i ∈ s, (((q i : ℂˣ) : ℂ) * ((p i : ℂˣ) : ℂ)⁻¹))⁻¹ *
      (((∏ i ∈ s, A i : ℂˣ) : ℂ) * ((∏ i ∈ s, B i : ℂˣ) : ℂ)⁻¹ * v) := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hu]
  push_cast [Units.coe_prod]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv, inv_inv]
  ring

theorem omegaG_blockTri_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, G PP ∈ blockTri (blkOf r t) ∧ H PP ∈ blockTri (blkOf r t) ∧ upperLeftBlock ha (G PP) = upperLeftBlock hb (H PP)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP))) * (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))⁻¹ * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) * (χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹)) : ℂˣ) : ℂ) * omegaG (datY a r t k ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb hak hbk Pg Q χ ξ G H hGH y

  have hlaw := GlobalTheory.T.typePlaces_localDatum_blockTriangular_law D a b r t k ha hb hak hbk Pg Q χ ξ G H y
    (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val)
    (fun PP hP => (hGH PP hP).1) (fun PP hP => (hGH PP hP).2.1) (fun PP hP => (hGH PP hP).2.2)
    (fun _ _ => rfl)
  exact collect_factors Pg
    (fun PP => ∏ c ∈ Finset.range k, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (G PP)))
    (fun PP => ∏ c ∈ Finset.range (k + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)))
    (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (G PP))) _ _ hlaw

end GlobalTheory.StepLaw
