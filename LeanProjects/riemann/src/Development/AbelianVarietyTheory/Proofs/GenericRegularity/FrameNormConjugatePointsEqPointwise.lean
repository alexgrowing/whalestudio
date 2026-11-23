import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fnConj_valAtCx_nrmC_eq_ptNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  intro E _ _ _ H Dw l Xo c r U _ xR fn _ hpin h yP hcb
  have hWD := GlobalTheory.TransferCompare.evalWD_framed Xo c
  have hgt : GenFromTest Xo c h := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 h
  have hcx : ValAtCx h yP := by
    intro Z P a n f hf
    have hT1 := hgt Z
    have hm := hcb Z P
    have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (yP Z P) := by
      obtain ⟨p, ψ, y', hy'⟩ := hT1
      exact ⟨p, (PAlg P).comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ (PAlg P) y' _ _ hy' hm⟩
    have key : evR Xo c f (yP Z P) = PAlg P (evR Xo c f (genFr h Z)) := by
      unfold evR evalAt
      rw [dif_pos hT2, dif_pos hT1]
      exact hWD f hf.1 _ _ _ _ _ _ _ (yP Z P) hT2.choose_spec.choose_spec.choose_spec
        (frMap_trans (Xo := Xo) (c := c) _ _ _ _ (PAlg P) _ _ _ hT1.choose_spec.choose_spec.choose_spec hm)
    rw [key]
    rfl
  refine ⟨?_, hcx, ?_⟩
  · intro Z G x P
    have hm : FrMap (conjAlg (sgOf P)) (yP Z P) (yP Z ((starRingEnd ℂ).comp P)) :=
      frMap_cancel (Xo := Xo) (c := c) _ _ _ (PAlg P) (conjAlg (sgOf P)) (genFr h Z) _ _ (hcb Z P)
        (hcb Z ((starRingEnd ℂ).comp P))
    unfold nrmC
    congr 1
    · exact Complex.norm_conj _
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun t : ℝ => t ^ (-exZ Dw G i)) (hpin.2 (sgOf P) (yP Z P) _ hm i)
  · intro Z P a n f hf
    show nrmC fn (yP Z) (wtZ a n) (AddMonoidAlgebra.single (wtZ a n) (evC h Z f)) P = _
    rw [nrmC_single, hcx Z P a n f hf]
    unfold ptNorm
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by cases i <;> rfl
    rw [e, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.FrameNorm
