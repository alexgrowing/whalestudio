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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_smul' {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  have h : jetLin (fun m => c * J m) = c • jetLin J := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply]
    rw [GlobalTheory.KerT.RatLaw.jetLin_monomial, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  simp only [jetMap, LinearMap.comp_apply, h, LinearMap.smul_apply]

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_substF {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : MvPolynomial (DVar ι a b) ℂ →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * ℓ (GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • GlobalTheory.KJInf.lft h (jetMap (fun m => ℓ (monomial m 1)) n (GlobalTheory.KJInf.lft g P)) := by
  have e1 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  have e2 : GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) = aeval (GlobalTheory.KerT.RatLaw.subst g h) := by
    refine algHom_ext fun v => ?_
    simp only [GlobalTheory.CompactHowe.substF_X, aeval_X, Matrix.transpose_apply]
  rw [jetMap_smul', GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [e1, e2]), mul_smul]
  rfl

open GlobalTheory.ColKer GlobalTheory.RowHoweAvg in
theorem UpperTheory.WildA.realTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.top t j)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.top t j)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t j) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t j) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).small k := by
  intro D T L sc G W U₀ N μ₀ hL t j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k _ k' _
  have hp : DefPair D.R.m (Pair.top t j) := hj
  have hj' : j < D.R.m := hj
  have hJ := (wtOK_of_defPair G _ hp).2
  have hr0 : Even (G.V (.top j)).rank := by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j
  have hr1 : Even (G.V (.top (j + 1))).rank := by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)
  have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
  have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have h1 : ∀ τ, e₁ τ = (wt G (.top (j + 1)) τ).detShift := fun τ => by
    have ea := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hS ▸ ha τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).1
    have h : (e₁ τ : ℚ) = ((wt G (.top (j + 1)) τ).detShift : ℤ) := by
      rw [he₁, this, ea]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have h2 : ∀ τ, e₂ τ = (nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift := fun τ => by
    have eb := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hT ▸ hb τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).2
    have h : (e₂ τ : ℚ) = (((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift : ℤ) : ℚ) := by
      rw [he₂, this, eb]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have hinv : GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ =
      fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k τ)⁻¹ := by
    funext τ
    rw [← realIn_coe, ← realIn_coe, map_inv, Pi.inv_apply, Matrix.coe_units_inv]
  have hne : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ≠ 0 := fun τ => by
    rw [← det_inB W.θ N, ← realIn_coe]
    exact (Matrix.isUnits_det_units _).ne_zero
  have hdi : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k⁻¹)).det =
      (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det⁻¹ := fun τ => by
    rw [← det_inB W.θ N, ← det_inB W.θ N, hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hm : ∀ m : Formalism.L2.Ker.DVar D.what₂.Tau (G.V (Pair.top t j).small).rank (G.V (Pair.top t j).big).rank →₀ ℕ,
      Finsupp.mapDomain (fvar G (Pair.top t j)) m = m := fun m => Finsupp.mapDomain_id
  have hs : GlobalTheory.FockReal.realSubst W N.frC (Pair.top t j) k k' =
      GlobalTheory.CompactHowe.substF (GlobalTheory.SeeSaw.inB W.θ (G.V (.top (j + 1))) (N.frC (.top (j + 1))) k')
        (fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ τ)ᵀ) := by
    rw [hinv]
    rfl
  refine LinearMap.ext fun v => Subtype.ext ?_
  have e0 := realAct_inv_coe W.θ N (.top j) k⁻¹ v
  rw [inv_inv] at e0
  simp only [hm, hs, LinearMap.comp_apply]
  rw [jetOp_coe hJ, realAct_inv_coe, jetOp_coe hJ]
  refine (jetMap_substF _ ℓ _ _ _ _).trans ?_
  erw [e0]
  rw [map_smul, map_smul, smul_smul]
  congr 1
  simp only [GlobalTheory.FockReal.realChar, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_inB, hdi, h1, h2]
  show (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ^ _ * _ * _ = _
  rw [zpow_sub₀ (hne τ), zpow_natCast, inv_pow, _root_.inv_zpow]
  have := pow_ne_zero (nuEnd G (.top t j) τ) (hne τ)
  field_simp
  try rfl
