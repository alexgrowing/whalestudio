import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  first | exact @GlobalTheory.LowFilt.tateIsoQ_y_cois | exact GlobalTheory.LowFilt.tateIsoQ_y_cois | (intros; apply GlobalTheory.LowFilt.tateIsoQ_y_cois <;> assumption)
