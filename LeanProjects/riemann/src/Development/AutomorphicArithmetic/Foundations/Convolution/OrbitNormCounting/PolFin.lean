import Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.NormCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem UpperTheory.ConvolutionTheory.G3.polFin :
    UpperTheory.ConvolutionTheory.G3.PolFin := by
  intro E _ _ _ hU n S hS C hC hC1
  choose γ hγ0 hγ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E n w (C w) (hC w)
  let g : Pl E → WithZero (Multiplicative ℤ) := fun w => if C w ⊆ GlobalTheory.LFun.KGL w n then 1 else γ w
  have hlev : ∀ w : Pl E, IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n) := fun w =>
    ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩
  refine (GlobalTheory.BCT.GeoFin.finite_ell_bounded E n S hS g
    (fun w => by by_cases h : C w ⊆ GlobalTheory.LFun.KGL w n <;> simp [g, h, hγ0])
    (hC1.mono fun w h => by simp [g, h])).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP, fun w hw => ?_⟩
  obtain ⟨y, hy, e⟩ := hPS w hw
  rw [← e]
  by_cases h : C w ⊆ GlobalTheory.LFun.KGL w n
  · simp only [g, if_pos h, inv_one]
    exact GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E n w (hlev w) y (h hy)
  · simp only [g, if_neg h]
    exact hγ w y hy
