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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.RigScale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem eSec_comp_of_cart {S : Scheme.{0}} {G : Over S} [GrpObj G] {z : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ) : eSec A ≫ φ = z ≫ eSec G := by
  have e := congrArg (fun q => q.left) (map_one (pushHom h (𝟙_ (Over (Sp ℂ)))))
  have e₁ : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def scale (u : HolUnif A L g) (c : ℂ) (hc : c ≠ 0) : HolUnif A L g :=
  { u with
    fr := fun j w => c * u.fr j w
    fr_hol := fun i => (u.fr_hol i).const_mul c
    fr_ne := fun i z h => mul_ne_zero hc (u.fr_ne i z h)
    fr_compat := fun i j z h => by
      rw [u.fr_compat i j z h]
      ring }

theorem scale_isAH {u : HolUnif A L g} {c : ℂ} (hc : c ≠ 0) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : (scale u c hc).IsAH Hm χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun l i z hz => ?_⟩
  show c * u.fr i z = _ * (c * u.fr i (z + (l : Fin g → ℂ)))
  rw [h.2.2.2 l i z hz]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.RigScale

namespace GlobalTheory.CompanionTheory.Ar.Sl

open GlobalTheory GlobalTheory.ArchMetricCompare RigScale

theorem exists_archFrame_of_isAH : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (g : ℕ) (u : HolUnif A (P.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A G z φ → u.IsAH Hm χ → Nonempty (ArchFrame P z g) := by
  intro S G _ _ P z A _ φ g u Hm χ cart ah
  have he : (u.ex 0).left ≫ φ = z ≫ eSec G := by
    have := eSec_comp_of_cart cart
    rw [show (u.ex 0).left = eSec A from GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u]
    exact this
  obtain ⟨i₀, h₀⟩ : ∃ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i :=
    (exists_chart P.isLB (((u.ex 0).left ≫ φ) (default : PrimeSpectrum ℂ))).imp
      fun _ h => (top_le_preimage_iff_mem _ _).2 h

  have hfr : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => i) :=
    fun i h => (le_pull_iff P.L φ _ _).2 h
  have hz : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      ⊤ ≤ z ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i) := fun i h =>
    (le_pull_iff P.L (eSec G) z _).2 (he ▸ h)
  have hrel : ∀ i, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
      valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val =
        valAt' ((u.ex 0).left ≫ φ) (P.L.U i ⊓ P.L.U i₀) (P.L.g i i₀).val *
          valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val := by
    intro i hi
    have hm : ⊤ ≤ z ⁻¹ᵁ ((P.L.pull (eSec G)).U (fun _ => i) ⊓ (P.L.pull (eSec G)).U (fun _ => i₀)) :=
      (top_le_preimage_inf _ _ _).2 ⟨hz i hi, hz i₀ h₀⟩
    have e := congrArg (fun a => valAt' z _ (Units.val a)) (P.rigGen (fun _ => i) (fun _ => i₀))
    have e2 := (valAt'_res z inf_le_left _ hm).symm.trans (e.trans ((valAt'_mul _ _ _ _).trans
      (congrArg₂ (· * ·) rfl (valAt'_res z inf_le_right _ hm))))
    rw [he]
    rw [← val_pull_g P.L (eSec G) z (fun _ => i) (fun _ => i₀) hm]
    exact e2
  have hn : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val ≠ 0 :=
    valAt'_unit_ne_zero z (hz i₀ h₀) _
  have hd := u.fr_ne (fun _ => i₀) 0 (hfr i₀ h₀)
  have hc : valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i₀).val / u.fr (fun _ => i₀) 0 ≠ 0 :=
    div_ne_zero hn hd
  refine ⟨{ A := A, φ := φ, cart := cart, u := scale u _ hc, Hm := Hm, χ := χ, ah := scale_isAH hc ah, rig := ?_ }⟩
  intro i hi
  have hi' : ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i := hi
  show _ / u.fr (fun _ => i₀) 0 * u.fr (fun _ => i) 0 = _
  have hm : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((P.L.pull φ).U (fun _ => i) ⊓ (P.L.pull φ).U (fun _ => i₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hfr i hi', hfr i₀ h₀⟩
  rw [u.fr_compat (fun _ => i) (fun _ => i₀) 0 hm, val_pull_g P.L φ _ (fun _ => i) (fun _ => i₀) hm, hrel i hi']
  field_simp

end GlobalTheory.CompanionTheory.Ar.Sl
