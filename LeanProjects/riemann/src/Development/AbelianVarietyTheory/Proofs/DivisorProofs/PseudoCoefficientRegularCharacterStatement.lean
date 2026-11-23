import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientRegularCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudo_coefficient_regular_character : DiscreteSeriesCharacter → ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ))) [μ.IsHaarMeasure]
    (f : GArch D.sp.cm.sig V.gram (placeOf D ρ) → ℂ), Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) →
    (haveI := (M.ds ρ).1; IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) f) →
    ∀ (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
    IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
    ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
    frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
    HasOrbInt μ s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  first | exact @GlobalTheory.EllipticOrb.orbInt_elliptic | exact GlobalTheory.EllipticOrb.orbInt_elliptic | (intros; apply GlobalTheory.EllipticOrb.orbInt_elliptic <;> assumption)
