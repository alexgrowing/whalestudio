import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsKinf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (g : GA D V) : Prop :=
  g ∈ GinfC V ∧ ∀ τ, ∃ b : Mat (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2, IsKC b ∧
    b * A τ = A τ * infMat D.sp.cm.sig V.gram (θ τ) g

def IsRealW (V W : HSp D) (x : WA V W) : Prop := x.map (finPart D) = 0

def IsRealDir (V W : HSp D) (L : ℝ →+ WA V W) : Prop := Continuous L ∧ ∀ t, IsRealW V W (L t)

def dRho (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun x => deriv (fun t : ℝ => Heisenberg₂ ψ V W (L t) f x) 0

def annOp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (J : WA V W →+ WA V W) (L : ℝ →+ WA V W)
    (f : WA V W → ℂ) : WA V W → ℂ :=
  fun x => dRho ψ V W L f x + Complex.I * dRho ψ V W (J.comp L) f x

def valTau (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) (a : AF D.host.F) : ℝ :=
  (θ τ (infPart D (algebraMap (AF D.host.F) (AE D) a))).re

structure IsFockCx (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V W : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ)
    (J : WA V W →+ WA V W) : Prop where
  cont : Continuous J
  real : ∀ x, IsRealW V W x → IsRealW V W (J x)
  sq : ∀ x, IsRealW V W x → J (J x) = -x
  symp : ∀ x y, IsRealW V W x → IsRealW V W y → sympl V W (J x) (J y) = sympl V W x y
  kcomm : ∀ k k', IsKinf θ V A k → IsKinf θ W B k' → ∀ x, IsRealW V W x →
    J (actHom V W k k' x) = actHom V W k k' (J x)
  defin : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x, IsRealW V W x →
    (∀ τ, 0 ≤ ε * valTau θ τ (sympl V W (J x) x)) ∧ ((∀ τ, valTau θ τ (sympl V W (J x) x) = 0) → x = 0)

def IsPolFock (ψ : AddChar (AF D.host.F) ℂ) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V W : HSp D)
    (A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ)
    (f : WA V W → ℂ) : Prop :=
  ∃ J : WA V W →+ WA V W, IsFockCx θ V W A B J ∧ ∃ N : ℕ, ∀ Ls : Fin N → (ℝ →+ WA V W),
    (∀ i, IsRealDir V W (Ls i)) → (List.ofFn Ls).foldr (fun L g => annOp ψ V W J L g) f = 0

structure KfinTied {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) where

  cpt : ∀ (V : HSp D) (τ : D.what₂.Tau),
    Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ
  cpt_gram : ∀ V : HSp D, V.SigOK → ∀ τ,
    (cpt V τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cpt V τ = gramAt D V τ

  bas : ∀ V : HSp D, Matrix (Fin V.rank) (Fin V.rank) D.host.E
  bas_unit : ∀ V : HSp D, V.SigOK → IsUnit (bas V).det

  bas_orth : ∀ V : HSp D, V.SigOK → ∀ i j, i ≠ j →
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (bas V) * V.gram * bas V) i j = 0

  cpt_bas : ∀ V : HSp D, V.SigOK → ∀ τ a i j,
    (cpt V τ * (bas V).map (tauE D τ)) a i ≠ 0 → (cpt V τ * (bas V).map (tauE D τ)) a j ≠ 0 → i = j

  kfin : AllSome (IsInfFam (D := D)) fun θ => ∀ (V W : HSp D), V.rank ≠ W.rank → V.SigOK → W.SigOK →
    ∀ Φ : X.Sch V W, Φ ∈ X.kfin V W ↔ IsPolFock Wl.ψ θ V W (cpt V) (cpt W) (Wl.evS V W Φ)

end Formalism.L2.Theta

end
