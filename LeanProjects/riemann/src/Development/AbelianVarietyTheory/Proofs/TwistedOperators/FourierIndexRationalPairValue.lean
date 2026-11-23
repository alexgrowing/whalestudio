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
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin N × Fin n) ℂ) := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X]
    obtain ⟨τ, a, b⟩ := p
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Matrix.one_apply, hx]) (by simp),
      Finset.sum_eq_single b (fun y _ hy => by simp [Matrix.one_apply, hy]) (by simp)]
    simp
  exact congrArg (fun f => f P) key

theorem mul_conjT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    M * Matrix.conjTranspose M = 1 := Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 h

theorem map_conj_mul_conjT {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M * Matrix.conjTranspose M = 1) :
    M.map (starRingEnd ℂ) * Matrix.conjTranspose (M.map (starRingEnd ℂ)) = 1 := by
  have e := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
  convert e using 2
  ext a b
  simp [Matrix.conjTranspose_apply]

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem conj_invT_of_unitary' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conjT_mul_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    Matrix.conjTranspose (compAt θ τ (Formalism.L2.Theta.mt V g)) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact h1

theorem om_pureTensorO_vac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (g : GA D A)
    (h : GA D WW) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) ∧
    (X.ω t).toSgn true ((ofSgn true A).symm g, h)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac)
        (GlobalTheory.CompactHowe.substF (fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW h)).map (starRingEnd ℂ))
          (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW X.vac := hI.isVac.2.theta
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  set v : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW h) with hv
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * v τ) ((ofSgn true A).symm g) h
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hsW, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hBW, Matrix.mul_one, Matrix.one_mul]) X.vac hf P
  refine ⟨hop.1, ?_⟩
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B v _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ =>
    conj_invT_of_unitary' (conjT_mul_compAt hθ hX.std.1 g τ)
  rw [funext hunit] at key
  rw [e1, e2]
  exact key

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem isAlgebraic_compAt_of_mem_GQ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {γ : GA D V}
    (hγ : γ ∈ GQ V) (τ : D.what₂.Tau) (a b : Fin V.rank) :
    IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V γ) a b) := by
  obtain ⟨γ₀, h0⟩ := GlobalTheory.Member.exists_isRat_of_mem_GQ V hγ
  have key : compAt θ τ (Formalism.L2.Theta.mt V γ) a b = tauE D τ (γ₀.1 a b) := by
    unfold compAt Formalism.L2.Theta.mt
    rw [h0]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  first
    | exact h.algHom (starRingEnd ℂ).toRatAlgHom
    | exact IsAlgebraic.map (starRingEnd ℂ).toRatAlgHom h
    | exact (isAlgebraic_algHom_iff (starRingEnd ℂ).toRatAlgHom (starRingEnd ℂ).injective).2 h

theorem jet_moved_vac_alg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t γ hγ a _ γ' hγ' a' _ _ _ k
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hom := hI.weil t
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A γ) with hu
  set hm : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ :=
    fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW γ')).map (starRingEnd ℂ) with hhm
  set H : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => Matrix.conjTranspose (hm τ) with hH
  set U : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => Matrix.conjTranspose (u τ) with hU
  set Q := GlobalTheory.CompactHowe.substF H U (MvPolynomial.monomial k 1) with hQdef
  have hHm : hm * H = fun _ => 1 := funext fun τ =>
    map_conj_mul_conjT (mul_conjT_of_unitary (conjT_mul_compAt hθ hX.stdW.1 γ' τ))
  have hUm : u * U = fun _ => 1 := funext fun τ => mul_conjT_of_unitary (conjT_mul_compAt hθ hX.std.1 γ τ)
  have hQ : GlobalTheory.CompactHowe.substF hm u Q = MvPolynomial.monomial k 1 := by
    rw [hQdef, GlobalTheory.CompactHowe.substF_mul, hHm, hUm, substF_one]
  have hact := om_pureTensorO_vac hX t γ γ' Q
  have hjet : pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac)
        (MvPolynomial.monomial k 1) 0 =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0 := by
    rw [← hQ]
    change pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
      ((X.ω t).toSgn true ((ofSgn true A).symm γ, γ') X.vac) _ 0 = _
    rw [← hact.2]
    exact hom.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) γ' hγ' _ hact.1
  have hHalg : ∀ τ a b, IsAlgebraic ℚ (H τ a b) := by
    intro τ a b
    have e : H τ a b = compAt W.θ τ (Formalism.L2.Theta.mt WW γ') b a := by
      simp [hH, hhm, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_compAt_of_mem_GQ hθ hγ' τ b a
  have hUalg : ∀ τ a b, IsAlgebraic ℚ (U τ a b) := by
    intro τ a b
    have e : U τ a b = starRingEnd ℂ (compAt W.θ τ (Formalism.L2.Theta.mt A γ) b a) := by
      simp [hU, hu, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_conj (isAlgebraic_compAt_of_mem_GQ hθ hγ τ b a)
  let e := Q.support.equivFin
  refine ⟨Q.support.card, fun p => MvPolynomial.coeff (e.symm p).1 Q, fun p => (e.symm p).1, fun p => ?_, fun p => ?_, ?_⟩
  · exact (GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic k (e.symm p).1).2 H U hHalg hUalg
  · exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero H U k (e.symm p).1
      (MvPolynomial.mem_support_iff.1 (e.symm p).2)
  · rw [hjet]
    calc pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0
        = ∑ x ∈ Q.support, MvPolynomial.coeff x Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x 1) 0 := by
          conv_lhs => rw [Q.as_sum]
          rw [map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show MvPolynomial.monomial x (MvPolynomial.coeff x Q) = MvPolynomial.coeff x Q • MvPolynomial.monomial x 1 by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
          rw [← Finset.sum_coe_sort]
          exact (Equiv.sum_comp e.symm (fun x : Q.support => MvPolynomial.coeff x.1 Q *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x.1 1) 0)).symm

end GlobalTheory.MovedJet

end
