import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.ArcCM.cfOf_linear_and_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ d a' n
  have hP : ∀ F ∈ sec Xo c a' n, ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁),
      algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (absA Dw a') := fun F hF =>
    GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF
  have hcomp : ∀ a : c.F, algebraMap c.F (ArcS Dw K₁) a =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)
        (algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a) := fun _ => rfl
  have hnum : ∀ F : sec Xo c a' n,
      algebraMap _ (ArcS Dw K₁) (arcNum (evR Xo c F.1 d.yF)) = evR Xo c F.1 d.yF := fun F =>
    (hP F.1 F.2).elim fun P hP' => by
      rw [← hP'.1, LinOfPoly.arcNum_map]
  have hadd : ∀ F G : sec Xo c a' n, arcNum (evR Xo c (F + G).1 d.yF) =
      arcNum (evR Xo c F.1 d.yF) + arcNum (evR Xo c G.1 d.yF) := fun F G =>
    LinOfPoly.inj _ K₁ (by
      rw [map_add, hnum, hnum, hnum, Submodule.coe_add, LinOfPoly.evR_add])
  have hsmul : ∀ (a : c.F) (F : sec Xo c a' n), arcNum (evR Xo c (a • F).1 d.yF) =
      algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a *
        arcNum (evR Xo c F.1 d.yF) := fun a F =>
    LinOfPoly.inj _ K₁ (by
      rw [hnum, Submodule.coe_smul, LinOfPoly.evR_smul, map_mul, hnum F, hcomp])
  refine ⟨⟨{ toFun := fun F => cfOf d.yF d.μ d.jj F.1, map_add' := ?_, map_smul' := ?_ }, fun F => rfl⟩, ?_⟩
  · intro F G
    simp only [cfOf]
    rw [hadd, MvPolynomial.coeff_add, HahnSeries.coeff_add]
  · intro a F
    simp only [cfOf]
    rw [hsmul, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul, LinOfPoly.laur_alg,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, RingHom.id_apply]
    simp [Algebra.smul_def]
  · intro F hF hne
    obtain ⟨P, hP1, hP2⟩ := hP F hF
    rw [← Finsupp.degree_eq_sum]
    by_contra hd
    apply hne
    simp only [cfOf]
    rw [← hP1, LinOfPoly.arcNum_map, hP2.coeff_eq_zero hd]
    rfl
