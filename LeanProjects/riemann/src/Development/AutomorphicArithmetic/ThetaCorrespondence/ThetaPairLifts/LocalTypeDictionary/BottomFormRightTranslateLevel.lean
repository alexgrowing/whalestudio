import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupFieldStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.BottomLevel
theorem rightTranslate_preserves_level : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (J : Subgroup (GA D WW)) (M₂ : IntermediateField ℚ ℂ), IsOpen (J : Set (GA D WW)) ∧ FiniteDimensional ℚ M₂ ∧
      ∀ t, ∀ κ ∈ J, κ ∈ GfC WW → ∃ ℓ ∈ M₂, ∀ P x, X.I W.ψ W.θ t P (x * κ) = ℓ * X.I W.ψ W.θ t P x := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hf : ∀ t, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) := fun t =>
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hX.is.fst t) hX.is.isVac.2.theta
  choose U hUo hU using fin_vec_fix hX
  refine ⟨⨅ t, U t, ⊥, ?_, inferInstance, fun t κ hκ hκf => ⟨1, one_mem _, fun P x => ?_⟩⟩
  · rw [Subgroup.coe_iInf]; exact isOpen_iInter_of_finite fun t => hUo t
  · have hfix := hU t κ (Subgroup.mem_iInf.1 hκ t) hκf
    have hW := hX.is.weil t
    have hpt := GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW W.θ hθ 1 (one_mem _) κ hκf
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P (hf t)
    have e1 : ∀ g, (X.ω t).toSgn true (1, κ) g = X.ω t (1, κ) g := by
      intro g; simp [GlobalTheory.Grid.WRep.toSgn]
    rw [one_mul]
    unfold Tri.I Tri.ker thetaKO
    congr 1
    funext g
    have hm : ((g, x * κ) : GA D A × GA D WW) = (g, x) * (1, κ) := by simp
    rw [hm, map_mul, Module.End.mul_apply, ← e1, hpt, e1, hfix]
end GlobalTheory.BottomLevel
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomForm_rightTranslate_level : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ (J : Subgroup (GA D WW)) (M₂ : IntermediateField ℚ ℂ), IsOpen (J : Set (GA D WW)) ∧ FiniteDimensional ℚ M₂ ∧
      ∀ t, ∀ κ ∈ J, κ ∈ GfC WW → ∃ ℓ ∈ M₂, ∀ P x, X.I W.ψ W.θ t P (x * κ) = ℓ * X.I W.ψ W.θ t P x := by
  first | exact @_root_.GlobalTheory.BottomLevel.rightTranslate_preserves_level | exact _root_.GlobalTheory.BottomLevel.rightTranslate_preserves_level | (intros; apply _root_.GlobalTheory.BottomLevel.rightTranslate_preserves_level <;> assumption)
end
