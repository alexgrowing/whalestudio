import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationIndependent
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_localization_independent : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  first | exact @GlobalTheory.LieSpanLoc.exists_smul_mem_span | exact GlobalTheory.LieSpanLoc.exists_smul_mem_span | (intros; apply GlobalTheory.LieSpanLoc.exists_smul_mem_span <;> assumption)
