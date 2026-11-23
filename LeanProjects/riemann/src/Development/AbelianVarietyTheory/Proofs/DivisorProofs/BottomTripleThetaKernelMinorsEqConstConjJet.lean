import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinorPolZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFormula.ConjJet

theorem dRho_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) =
      fun w => starRingEnd ℂ (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f w) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isFockVacAt_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (f : WO S T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T f) (τ : D.what₂.Tau)
    (hv : IsFockVacAt (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-1) 1) f) :
    IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (f w)) := by
  intro z
  have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-1) 1) z f = 0 := hv z
  have hJ : cplxO (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) z = -cplxO 1 1 z := by
    simp [cplxO]
  unfold annih at h0 ⊢
  rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hf] at h0
  rw [dRho_conj hψ, dRho_conj hψ]
  funext x
  have h2 := congrFun h0 x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
  have e := congrArg (starRingEnd ℂ) h2
  simp only [map_add, map_mul, map_neg, Complex.conj_I, map_zero] at e
  linear_combination e

theorem map_conj_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : Tup D a d n) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.NormSum.minorPol D U) = GlobalTheory.NormSum.minorPol D U := by
  simp only [GlobalTheory.NormSum.minorPol, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext i i' : 2
  simp

theorem ker_minorF_eq_conj_jet : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil),
    IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) → ∀ n₀ : D.what₂.Tau → ℕ,
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (a d : ℕ) (n : D.what₂.Tau → ℕ) (ea : a = A.rank) (ed : d = WW.rank), n = n₀ →
      ∀ (s : T) (g : GA D WW) (y : GA D A), g ∈ GfC WW → y ∈ GfC A → ∀ Tu : Tup D a d n,
        X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed Tu) g y =
          Ω * starRingEnd ℂ (Formalism.MainNotions.GL3Theta.applyAt0 D (GlobalTheory.NormSum.minorPol D Tu)
            (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w))) := by
  intro D T Lc sc G W hψ i j A A' WW X hX r rc hr hrc n₀
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  obtain ⟨c₁, hc₁, H⟩ := GlobalTheory.NormDictEx.Jets.fock_minorPol_zero W.ψ W.θ A WW rfl rfl n₀ r rc hψ hθ hX.std.1 hX.stdW.1 hr hrc
  refine ⟨starRingEnd ℂ c₁, (map_ne_zero _).2 hc₁, ?_⟩
  intro a d n ea ed hn s g y hg hy Tu
  subst ea ed hn
  have hom := hI.weil s
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have hy' : (GlobalTheory.Grid.ofSgn true A).symm y ∈ GfC (GlobalTheory.Grid.neg A) := hy
  have hmove := GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω s).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) X.rW.s (X.f s) hf hv _ hy' g hg
  have hcomm := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω s).toSgn true) hom W.θ hθ _ hy' g hg
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s) (GlobalTheory.BotFormula.minorF rfl rfl Tu) hf
  set F : WO A WW → ℂ := X.ω s (y, g) (X.f s) with hF
  have hF1 : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW F := hmove.1
  have hF2 : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-1) 1) F := fun τ => by
    have h := hmove.2 τ
    rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
    exact h
  have hJ := H (fun w => starRingEnd ℂ (F w))
    (GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW F from hF1))
    (fun τ => isFockVacAt_conj hψ hθ A WW F hF1 τ (hF2 τ)) Tu
  have hP : MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.BotFormula.minorF (rfl : A.rank = A.rank) (rfl : WW.rank = WW.rank) Tu) =
      GlobalTheory.BotFormula.minorF rfl rfl Tu := by
    unfold GlobalTheory.BotFormula.minorF
    rw [MvPolynomial.map_rename, map_conj_minorPol]
  have hc := GlobalTheory.FockNegSubst.pureTensorO_negSp_map_conj W.ψ W.θ A WW hψ hθ (fun _ => 1) (fun _ => 1) F
    (GlobalTheory.BotFormula.minorF rfl rfl Tu)
  rw [hP] at hc
  have hk : X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl Tu) g y =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B F
        (GlobalTheory.BotFormula.minorF rfl rfl Tu) 0 := congrFun hcomm 0
  rw [hk, e1, e2, e3, e4, ← map_mul, ← hJ]
  exact congrFun hc 0

end GlobalTheory.BotFormula.ConjJet

end
