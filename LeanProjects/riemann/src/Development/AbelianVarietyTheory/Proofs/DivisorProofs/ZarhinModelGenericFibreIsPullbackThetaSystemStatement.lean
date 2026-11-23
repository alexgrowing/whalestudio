import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinModelGenericFibreIsPullbackThetaSystem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinModel_genericFibre_isPullback_thetaSystem : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE), X₁.S.Over₀ Y U₀ → ∃ ψ : ((Over.pullback Y.pt).obj O.G).left ⟶ X₁.ρ.P.A.left, IsGrpPullback ((Over.pullback Y.pt).obj O.G) X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) ψ ∧ LBIso (O.L.L.pull (pullback.fst O.G.hom Y.pt)) (X₁.ρ.P.L.pull ψ) ∧ ∀ f : X₁.ρ.P.A ⟶ X₁.ρ.P.A, IsMonHom f → ∃ F : O.G ⟶ O.G, IsMonHom F ∧ ((Over.pullback Y.pt).map F).left ≫ ψ = ψ ≫ f.left := by
  first | exact @GlobalTheory.ZH.GenFib.genFib_pullback | exact GlobalTheory.ZH.GenFib.genFib_pullback | (intros; apply GlobalTheory.ZH.GenFib.genFib_pullback <;> assumption)
