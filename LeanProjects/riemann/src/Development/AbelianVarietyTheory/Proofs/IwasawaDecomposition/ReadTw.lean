import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def ReadTw (D : D7) (a : D.nd.Loc) : Prop :=
  ∃ (φ : FractionRing (D.ntw.O0 (D.ntw.twOf a)) →+* Qbar (D.ntw.l (D.ntw.twOf a)))
    (ι : Qbar (D.ntw.l (D.ntw.twOf a)) ≃+* ℂ),
    (∀ z : ℤ_[D.ntw.l (D.ntw.twOf a)], φ (algebraMap (D.ntw.O0 (D.ntw.twOf a)) _
        (algebraMap ℤ_[D.ntw.l (D.ntw.twOf a)] (D.ntw.O0 (D.ntw.twOf a)) z)) =
      algebraMap ℚ_[D.ntw.l (D.ntw.twOf a)] (Qbar (D.ntw.l (D.ntw.twOf a))) (z : ℚ_[D.ntw.l (D.ntw.twOf a)])) ∧
    (∀ x : ↥D.LL0, ι (φ ((if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) x)) =
      embLL0 D x) ∧
    ∀ y : D.ntw.O0 (D.ntw.twOf a), ι (φ (algebraMap _ (FractionRing (D.ntw.O0 (D.ntw.twOf a))) y)) =
      iotaO D.nd D.naut a (D.ntw.twist₂ a y)

end GlobalTheory.RowTriple

end
