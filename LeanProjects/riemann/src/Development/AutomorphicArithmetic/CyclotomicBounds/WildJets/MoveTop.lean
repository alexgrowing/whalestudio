import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealTop
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.AttExp
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.moveTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} {N : Std G U₀} (Z : Normal W N) {μ₀ : T}, L.Is μ₀ → ∀ (t t' : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (d : FinDatum G t (GlobalTheory.ChiGrid.Pair.top t' j)) (x r : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (y r' : FinPt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big)
        (U : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).small).rank) D.host.E) (U' : Matrix.unitaryGroup (Fin (G.V ((GlobalTheory.ChiGrid.Pair.top t' j)).big).rank) D.host.E),
        GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).small) r U → GlobalTheory.RatMoveJets.RatCoord _ (N.fr ((GlobalTheory.ChiGrid.Pair.top t' j)).big) r' U' →
        Z.kkMap 1 d (r * x) (r' * y) ∘ₗ rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).small) (Unitary.toUnits U) =
          rhoVr (tauE D) (wt G ((GlobalTheory.ChiGrid.Pair.top t' j)).big) (Unitary.toUnits U') ∘ₗ Z.kkMap 1 d x y := by
  intro D T L sc G W U₀ N Z μ₀ hL t t' j hj d x r y r' U U' hU hU'
  have hp : DefPair D.R.m (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T) := hj
  have hω := W.om_is (GlobalTheory.ChiGrid.Pair.top t' j) hj
  obtain ⟨a, b, e₁, e₂, ha, hb, he₁, he₂⟩ := UpperTheory.WildA.expEx (G := G) hL _ hp
  obtain ⟨γ, hγ, k, hk, hrk, hρ⟩ := UpperTheory.WildA.ratReal W N.fr _ r U hU
  obtain ⟨γ', hγ', k', hk', hrk', hρ'⟩ := UpperTheory.WildA.ratReal W N.fr _ r' U' hU'
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W Z hp d (Z.hasVec_of_defPair hL hp d)
  have hB : ∀ X, DefNode D.R.m X → ∀ τ, (N.frC X τ)ᴴ * gramAt D (G.V X) τ * N.frC X τ = 1 := fun X hX τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on X hX)
  have hF : ∀ Q, IsThetaFunO W.ψ _ _ (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) := fun Q =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ h1 Q
  have haut : ∀ Q g h, W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) (γ * g) (γ' * h) =
      W.ker (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q) g h := by
    intro Q g h
    show thetaKO (W.om (.top t' j)) (γ * g) (γ' * h) _ = thetaKO (W.om (.top t' j)) g h _
    have e : ((γ * g, γ' * h) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) = (γ, γ') * (g, h) := rfl
    unfold thetaKO
    rw [e, map_mul]
    exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ (hF Q))
  let ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t' j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t' j)).rank →ₗ[ℂ] ℂ :=
    { toFun := fun Q => kerFin W (GlobalTheory.ChiGrid.Pair.top t' j) (fockIn W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) Q)
        (x * N.u _) (y * N.u _)
      map_add' := fun P Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]
      map_smul' := fun c Q => by
        simp only [kerFin, GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have key := UpperTheory.WildA.realTop (W := W) N hL t' j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have tab : jetTab W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) (Z.vec d) (r * x * N.u _) (r' * y * N.u _) =
      fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t' j) e₁ e₂ k k' *
        ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t' j) k k'
          (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t' j))) 1)) := by
    funext m
    rw [jetTab, kerFin, mul_assoc r, mul_assoc r', hrk, hrk', haut]
    exact GlobalTheory.FockReal.ker_fockIn_real hL W N.frC hp hB a b ha hb e₁ e₂ he₁ he₂ _ h1 h2 k hk k' hk' _ _ _
  have hid : GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k ∘ₗ
      GlobalTheory.DefStep.realAct W.θ N.fr (GlobalTheory.ChiGrid.Pair.top t' j : GlobalTheory.ChiGrid.Pair T).small k⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hρ, ← hρ', Normal.kkMap, Normal.kkMap, fockComp, fockComp, tab, key, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.comp_assoc, LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rfl
