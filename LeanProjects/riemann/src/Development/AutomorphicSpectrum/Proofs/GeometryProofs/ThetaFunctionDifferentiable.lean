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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem isFn_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  intro S G _ _ P z g a n s θ hθ w₀
  have hm : a.pt w₀ (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hi : ⊤ ≤ a.pt w₀ ⁻¹ᵁ P.L.U i := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi'
  let W : G.left.Opens := LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i)
  let Q : a.A.left.Opens := (P.L.pull a.φ).U (fun _ => i)
  let C : Set (Fin g → ℂ) := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ Q}
  have hCpt : ∀ w, w ∈ C → ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := fun w h y hy =>
    Set.mem_iInter.1 (h hy) PUnit.unit
  have hptC : ∀ w, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → w ∈ C := fun w h y hy =>
    Set.mem_iInter.2 fun _ => h hy
  have hCV : ∀ w, w ∈ C → ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (a.φ ⁻¹ᵁ W) := fun w h y hy =>
    Set.mem_iInter.2 fun _ => hCpt w h hy
  have ho : IsOpen C := (a.u.hol Q 0).1
  have hv : DifferentiableOn ℂ (fun w => valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i))) C :=
    (a.u.hol _ _).2.mono hCV
  have hfr : DifferentiableOn ℂ (fun w => a.u.fr (fun _ => i) w ^ n) C := (a.u.fr_hol _).pow n
  have hne : ∀ w ∈ C, a.u.fr (fun _ => i) w ^ n ≠ 0 := fun w hw => pow_ne_zero n (a.u.fr_ne _ w hw)
  have hq : DifferentiableOn ℂ θ C := by
    refine (hv.mul (hfr.inv hne)).congr fun w hw => ?_
    have e := hθ i w (hCpt w hw)
    have e' : valF (a.pt w) W (s.f fun _ => i) = valAt' (a.pt w) W (s.f fun _ => i) := rfl
    have e4 : valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i)) = θ w * a.u.fr (fun _ => i) w ^ n :=
      (GlobalTheory.valAt'_comp (a.u.ex w).left a.φ W (s.f fun _ => i)).trans (e'.symm.trans e)
    exact (mul_inv_cancel_right₀ (hne w hw) (θ w)).symm.trans (congrArg (· * (a.u.fr (fun _ => i) w ^ n)⁻¹) e4.symm)
  exact (hq.differentiableAt (ho.mem_nhds (hptC w₀ hi)))

end GlobalTheory.CompanionTheory.Ar.Sl
