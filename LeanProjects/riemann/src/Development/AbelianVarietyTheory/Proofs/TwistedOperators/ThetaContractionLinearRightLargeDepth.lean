import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.Unf
open GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConLinR

section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem contr_lin_right (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ}
    {Ξ Ξ' : WO S B'.V₀ → ℂ} (c : ℂ) (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (hΞ : IsThetaFunO ψ S B'.V₀ Ξ)
    (hΞ' : IsThetaFunO ψ S B'.V₀ Ξ') (u : WO B.A S) (v : WO S B'.A) :
    contr l S vL Ξ₁ (c • Ξ + Ξ') u v = c * contr l S vL Ξ₁ Ξ u v + contr l S vL Ξ₁ Ξ' u v := by
  have iX := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL h₁ hΞ u v
  have iY := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL h₁ hΞ' u v
  simp only [GlobalTheory.Unf.contr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
  rw [integral_add (by simpa only [mul_assoc] using iX.const_mul c) iY, ← integral_const_mul]
  simp only [mul_assoc]

theorem flatFB_lin (hψ : IsStdChar D ψ (-1)) {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (st : StepFB ψ J B)
    {X Y : WO J.W B.V → ℂ} (c : ℂ) (hX : IsThetaFunO ψ J.W B.V X) (hY : IsThetaFunO ψ J.W B.V Y) :
    flatFB st (c • X + Y) = c • flatFB st X + flatFB st Y := by
  rw [(GlobalTheory.FlatAdd.flatFB_add_smul D (GlobalTheory.Unf.Flat.flatLaw D) ψ hψ σ J B st (c • X) Y
    (GlobalTheory.OrientedHeis.theta_smul c hX) hY).1,
    (GlobalTheory.FlatAdd.flatFB_add_smul D (GlobalTheory.Unf.Flat.flatLaw D) ψ hψ σ J B st X X hX hX).2 c]

theorem theta_flatFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (st : StepFB ψ J B) {X : WO J.W B.V → ℂ}
    (hX : IsThetaFunO ψ J.W B.V X) : IsThetaFunO ψ J.W₀ B.V₀ (flatFB st X) :=
  (((GlobalTheory.FinPl.flatLaws_all D) ψ (fun _ => True)).2 σ J B st).Heisenberg₂.theta X hX

theorem theta_flatBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (st : StepBF ψ B J) {X : WO B.V J.W → ℂ}
    (hX : IsThetaFunO ψ B.V J.W X) : IsThetaFunO ψ B.V₀ J.W₀ (flatBF st X) :=
  (((GlobalTheory.FinPl.flatLaws_all D) ψ (fun _ => True)).1 ρ B J st).Heisenberg₂.theta X hX

end Gen

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem fock_lin (p : Pair T) {φ φ' : WO (G.pS p) (G.pT p) → ℂ} (c : ℂ) (hφ : IsThetaFunO W.ψ _ _ φ)
    (hφ' : IsThetaFunO W.ψ _ _ φ') (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • φ + φ') Q = c • W.fock p φ Q + W.fock p φ' Q := by
  simp only [GridData.Weil.fock]
  rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ (GlobalTheory.OrientedHeis.theta_smul c hφ) hφ' Q,
    GlobalTheory.FiniteFock.pureTensorO_smul]

theorem om_fock_theta (p : Pair T) (hp : p.InRange D.R.m) (g : GA D (G.pS p) × GA D (G.pT p))
    {φ : WO (G.pS p) (G.pT p) → ℂ} (hφ : IsThetaFunO W.ψ _ _ φ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    IsThetaFunO W.ψ _ _ (W.om p g (W.fock p φ Q)) :=
  (W.om_is p hp).om_pres g _ (GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hφ Q)

end Grid

end GlobalTheory.ConLinR

namespace GlobalTheory.ConLinR
section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem contrLin_one_of (ch : Choice R) : ContrLin ch 1 := by
  intro j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  obtain ⟨a, ha'⟩ := a
  simp only at ha
  subst ha
  have h0 : ¬ (j + 2 * 0 + 2 = D.R.m) := by omega
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨r, hr⟩ := hj; obtain ⟨s, hs⟩ := hm; omega
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, ha'⟩ := by simp
  have hin0 : (Pair.mu t D.R.m j : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have hin1 : (Pair.mu t D.R.m (j + 1) : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  simp only [conAt, h0, hj', dite_false, dite_true, ↓reduceDIte]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  simp only [fock_lin ch.W (Pair.mu t D.R.m (j + 1)) c hφ hφ', map_add, map_smul]
  erw [flatFB_lin ch.W.ψ_std, contr_lin_right ch.W.ψ_std]
  case hX => exact om_fock_theta ch.W _ hin1 _ hφ _
  case hY => exact om_fock_theta ch.W _ hin1 _ hφ' _
  case h₁ =>
    refine theta_flatBF (B := besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ ?_
    exact om_fock_theta ch.W _ hin0 _ (hΦ ⟨j, by omega⟩) _
  case hΞ =>
    refine theta_flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ ?_
    exact om_fock_theta ch.W _ hin1 _ hφ _
  case hΞ' =>
    refine theta_flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ ?_
    exact om_fock_theta ch.W _ hin1 _ hφ' _

end Main

theorem contrLin_one_big : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 1 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => contrLin_one_of ch⟩⟩

end GlobalTheory.ConLinR
