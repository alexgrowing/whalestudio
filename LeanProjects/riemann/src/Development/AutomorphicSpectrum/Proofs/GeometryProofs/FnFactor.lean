import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Fac

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

private theorem eq_of_sp_complex_pts (y y' : ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) : y = y' := by
  have e : ∀ p : PrimeSpectrum ℂ, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime p.asIdeal
  exact PrimeSpectrum.ext (R := ℂ) ((e y).trans (e y').symm)

theorem fn_factor (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ)
    (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) (hθ : a.IsFn s θ)
    (l : a.u.Λ) (w : Fin g → ℂ) :
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  obtain ⟨-, -, -, hfr⟩ := a.ah
  obtain ⟨x0⟩ : Nonempty ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) :=
    ⟨(IsLocalRing.closedPoint ℂ : PrimeSpectrum ℂ)⟩
  obtain ⟨i, hi⟩ : ∃ i : P.L.ι, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt w).base).obj (P.L.U i) := by
    have hx : (a.pt w).base x0 ∈ (⨆ j, P.L.U j) := by
      rw [P.isLB.cover]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine ⟨j, fun y _ => ?_⟩
    rw [eq_of_sp_complex_pts y x0]
    exact hj
  have hz : ∀ v : Fin g → ℂ, ⊤ ≤ (TopologicalSpace.Opens.map (a.pt v).base).obj (P.L.U i) →
      ⊤ ≤ (TopologicalSpace.Opens.map (CategoryTheory.Over.Hom.left (a.u.ex v)).base).obj
        ((P.L.pull a.φ).U fun _ => i) := by
    intro v hv y hy
    exact Set.mem_iInter.2 fun _ => hv hy
  have hpt : a.pt (w + (l : Fin g → ℂ)) = a.pt w := by
    have h1 : a.u.ex (l : Fin g → ℂ) = 1 := (a.u.ker _).2 l.2
    change CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex (w + (l : Fin g → ℂ)))) a.φ =
      CategoryTheory.CategoryStruct.comp (CategoryTheory.Over.Hom.left (a.u.ex w)) a.φ
    rw [a.u.ex_add, h1, _root_.mul_one]
  have hi' : ⊤ ≤ (TopologicalSpace.Opens.map (a.pt (w + (l : Fin g → ℂ))).base).obj (P.L.U i) := by
    rw [hpt]
    exact hi
  have hA := hθ i w hi
  have hB := hθ i (w + (l : Fin g → ℂ)) hi'
  rw [hpt] at hB
  have hE := hB.symm.trans hA
  have hF := a.u.fr_ne (fun _ => i) (w + (l : Fin g → ℂ)) (hz _ hi')
  have hw : a.u.fr (fun _ => i) w =
      (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) *
        a.u.fr (fun _ => i) (w + (l : Fin g → ℂ)) := hfr l (fun _ => i) w (hz w hi)
  rw [hw, mul_pow] at hE
  apply mul_right_cancel₀ (pow_ne_zero n hF)
  rw [hE]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.Fac
