import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsTopNodeOntoUnitaryHaarUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockComponentTransportedPointsEqJetOperatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.AvgCol

theorem avg_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL j hj Q Λ
  obtain ⟨hr, huniq⟩ := GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique S hL j hj.le
  let r : GinfC (G.V (.top j)) →* (D.what₂.Tau → GL (Fin (G.V (.top j)).rank) ℂ) :=
    (realIn W.θ S.N.fr (.top j)).comp (GinfC (G.V (.top j))).subtype
  have hrk : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank ∧ 0 < (G.V (.top j)).rank := by
    rw [(node_isV G hL (X := .top j) (show j ≤ D.R.m by omega)).rank,
      (node_isV G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).rank]
    simp only [Node.rank, rankX, rankP, nRk]
    constructor
    · nlinarith
    · omega
  obtain ⟨hab, ha⟩ := hrk
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) :=
    (wtOK_of_defPair G (.top μ0 j) (show j + 1 ≤ D.R.m from hj)).2
  by_cases hex : ∃ κ₀ : Measure (GinfC (G.V (.top j))), κ₀.IsHaarMeasure ∧ IsProbabilityMeasure κ₀
  · obtain ⟨κ₀, h1, h2⟩ := hex
    haveI := h1
    haveI := h2
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional D.what₂.Tau _ _ hab ha (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) hJ
      (GinfC (G.V (.top j))) κ₀ r hr (frChInv W S.N j Q) Λ
    refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
    obtain rfl := huniq κ κ₀ hκ hκp h1 h2
    let ℓ : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₗ[ℂ] ℂ :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS (.top t j)) (G.pT (.top t j)) => ℂ) 0).comp
        ((W.om (.top t j) (G.toPair (.top t j) (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))))).comp
          ((W.fock (.top t j) (movedVec t S d)).comp (frCh W S.N j).toLinearMap))
    have hℓ : ∀ P, ℓ P = W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (frCh W S.N j P))
        (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := fun P => rfl
    have e1 : ∀ k : GinfC (G.V (.top j)),
        W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j))))⁻¹ v) =
          (∏ τ, ((r k τ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ ((nuEnd G (.top μ0 j) τ : ℤ) - (wt G (.top j) τ).detShift) *
              ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
            ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((r k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ) (frChInv W S.N j Q)) *
            Λ (rhoK (wt G (.top j)) (invTrK (r k⁻¹)) v) := by
      intro k
      rw [GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel S hL j hj t d hd Q x k k.2 h, hℓ]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), hΛ' ℓ (realIn W.θ S.N.fr (.top (j + 1)) h) v,
      GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator S hL j hj t d hd x (finOf _ h)]
    have e2 : realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ =
        rhoK (wt G (.top (j + 1))) (invTrK (realIn W.θ S.N.fr (.top (j + 1)) h)⁻¹) := by
      simp only [realAct, MonoidHom.comp_apply, map_inv]
    rw [e2]
    rfl
  · exact ⟨0, fun t _ d _ κ hκ hκp => absurd ⟨κ, hκ, hκp⟩ hex⟩

end GlobalTheory.AvgCol

end
