import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.FockConjNeg

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO (GlobalTheory.Grid.neg S) T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id g) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z g) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem cplxO_neg_left {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT u = -cplxO sS sT u := by
  simp [cplxO, Matrix.mul_neg, smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem aPlus_cj_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {g : WO (GlobalTheory.Grid.neg S) T → ℂ} (hg : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T g) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cj id (aPlus (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-sS) sT) u g) =
      aPlus (heisO ψ S T) θ τ (cplxO sS sT) u (cj id g) := by
  have hn := GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hg τ (cplxO sS sT u)
  unfold aPlus crea
  rw [cplxO_neg_left, hn, dRho_cj_neg hψ, dRho_cj_neg hψ]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_sub, map_neg,
    map_inv₀, Complex.conj_ofReal, Complex.conj_I]
  ring

end GlobalTheory.FockConjNeg

namespace GlobalTheory.FockConjNeg

variable {D : D7}

theorem fock_true_eq_ptF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.Grid.fock ψ θ true S T f P = ptF ψ θ (frSgn true (Fr.ofModel S.M)) (Fr.ofModel T.M) f P := by
  have hc : (frSgn true (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => cart_frSgn true (Fr.ofModel S.M) τ
  unfold ptF
  rw [hc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem cj_ptF_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} (A : Fr V) (B : Fr W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg V) W f)
    (P : PolF D W.rank V.rank) :
    cj id (ptF ψ θ (frSgn true A) B f P) = ptF ψ θ A B (cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have hcf : IsThetaFunO ψ V W (cj id f) := GlobalTheory.CjNeg.theta_negS' hψ hf
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, ← mul_one (MvPolynomial.C a), ← mul_one (MvPolynomial.C (starRingEnd ℂ a)),
      GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one, GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | add p q hp hq =>
    rw [map_add, GlobalTheory.FockAdjoint.ptF_add, GlobalTheory.FockAdjoint.ptF_add, ← hp, ← hq]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.map_X, mul_comm, GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ (frSgn true A) B hf, mul_comm,
      GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ A B hcf, ← hp, cart_frSgn]
    exact aPlus_cj_neg hψ hθ (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn true A) B hf p) v.1 _ _ _

theorem fock_neg_cj : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  intro D S T ψ θ f hψ hθ hf P
  rw [fock_true_eq_ptF, cj_ptF_neg hψ hθ _ _ hf]
  rfl

end GlobalTheory.FockConjNeg
