import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportSourceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInductionOnSplitPlaceSupportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedAlg

theorem suppSplit_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ), 0 < N → ∀ g ∈ GfC A, ∀ g' ∈ GfC WW,
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom A) g : Matrix (Fin A.rank) (Fin A.rank) _) →
      GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N ((finHom WW) g' : Matrix (Fin WW.rank) (Fin WW.rank) _) →
      ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
        (∀ p, (w p).map (infPart D) = 0) ∧
        X.ω t (g, g') X.vac = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX t N hN g hg g' hg' hs hs'
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) := fun u v hu hv =>
    GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 _ _ u v hu hv
  have hmul : ∀ p q : GA D A × GA D WW, IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t p X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t q X.vac) →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (p * q) X.vac) := by
    rintro ⟨x, h⟩ q hp hq
    rw [map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t x h hp hq
  have hone : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac) := by
    rw [map_one, Module.End.one_apply]
    refine ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => by simp, ?_⟩
    simp [GlobalTheory.SplitScalar.heisO_zero]
  have hW : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, g') X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport WW N (fun h => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_idempotent hP hI hL hX t N e P hP' hN' x hx hsx) g' hg' hs'
  have hA : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (g, 1) X.vac) :=
    GlobalTheory.T.unitary_induction_on_splitPlaceSupport A N (fun x => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, 1) X.vac)) hone
      (fun x y hx hy => by simpa using hmul _ _ hx hy)
      (fun e P hP' hN' x hx hsx => GlobalTheory.T.theta_local_support_source hP hI hL hX t N e P hP' hN' x hx hsx) g hg hs
  have := hmul _ _ hA hW
  simp only [Prod.mk_mul_mk, mul_one, one_mul] at this
  exact this

end GlobalTheory.MovedAlg

end
