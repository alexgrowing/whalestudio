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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.VacTranslateLeft

theorem exists_open_fix_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT hS hT f₀ hvac u hu
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS.1 hT.1 u hu
  have hN : 0 < 2 * (2 * 2) * M * M := by positivity
  have hev := GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u hu (2 * (2 * 2) * M * M) hN
  have hc : Filter.Tendsto (fun κ : GA D S => (κ, (1 : GA D T))) (𝓝 1) (𝓝 1) := by
    have := (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))).tendsto (1 : GA D S)
    simpa only [Prod.mk_one_one, id] using this
  have hev' := hc.eventually hev
  have key : ∃ n : ℕ, ∀ κ ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial κ →
      ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T κ 1 u = u + (2 * (2 * 2) * M * M) • l := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    obtain ⟨l, hl, e⟩ := hn
    exact hkne n l hl e
  obtain ⟨n, hn⟩ := key
  refine ⟨GlobalTheory.VacFixTarget.congGroup S n.factorial, GlobalTheory.VacFixTarget.isOpen_congGroup S n.factorial_pos,
    fun κ hκc hκ => ?_⟩
  obtain ⟨l, hl, e⟩ := hn κ hκ hκc
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have e2 : (2 * (2 * 2) * M * M) • l = 2 • ((2 * 2) • (M • (M • l))) := by
    simp only [smul_smul]
    congr 1
    ring
  have hu' : (2 * 2) • (M • (M • l)) ∈
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl M) M) _
  have hs : ψ (symplOH S T u (2 • ((2 * 2) • (M • (M • l))))) = 1 := by
    rw [two_nsmul, GlobalTheory.SplitScalar.symplOH_add_right, GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.Mem.CoefInv.symplO_nsmul,
      ← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_comm M (2 * 2) u]
    exact GlobalTheory.VacTranslate.psi_four_eq_one hvac.2.lat.1 hw₀ hMu (AddSubgroup.nsmul_mem _ hl M)
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T u (2 • ((2 * 2) • (M • (M • l)))) f₀
  rw [hvac.2.lat.1 _ hu', hs, one_smul] at h
  rw [e, e2, h]

end GlobalTheory.VacTranslateLeft

end
