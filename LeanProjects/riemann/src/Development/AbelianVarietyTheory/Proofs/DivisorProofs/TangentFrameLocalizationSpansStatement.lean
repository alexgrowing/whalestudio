import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationSpans
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
theorem _root_.GlobalTheory.T.tangent_frame_localization_spans : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  first | exact @GlobalTheory.isLieBasis_of_local_restrict | exact GlobalTheory.isLieBasis_of_local_restrict | (intros; apply GlobalTheory.isLieBasis_of_local_restrict <;> assumption)
