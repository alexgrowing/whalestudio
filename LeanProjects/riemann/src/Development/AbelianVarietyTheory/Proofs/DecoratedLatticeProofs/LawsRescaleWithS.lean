import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (s : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (s • f) = s • heisO ψ S T w f := by
  funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7} {m n : ℕ}

theorem dRho_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (s : ℂ) (f : Mx D m n → ℂ) :
    Datum.dRho hs θ τ z (s • f) = s • Datum.dRho hs θ τ z f := by
  funext x
  simp only [Datum.dRho, hh, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field _

theorem aPlusAll_smul (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (hh : ∀ w (s : ℂ) f, hs w (s • f) = s • hs w f) (θ : InfFam D)
    (J : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ → Matrix (Fin m) (Fin n) ℂ)
    (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (k) (s : ℂ) (f : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (s • f) = s • aPlusAll hs θ J B B' k f := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hh, smul_sub, smul_comm s]

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (k : ι →₀ ℕ) (s : ℂ) (f : X → ℂ) : opPow A k (s • f) = s • opPow A k f := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i (s : ℂ) f, A i (s • f) = s • A i f)
    (s : ℂ) (f : X → ℂ) : pureTensorL A (s • f) = s • pureTensorL A f := by
  unfold pureTensorL
  have : (fun k : ι →₀ ℕ => opPow A k (s • f)) = s • fun k => opPow A k f := by
    funext k; exact opPow_smul A hA k s f
  rw [this, map_smul]

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

variable {D : D7}

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (s : ℂ) (f : WO S T → ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (s • f) = s • pureTensorO ψ θ S T sS sT BS BT f :=
  pureTensorL_smul _ (aPlusAll_smul _ (heisO_smul ψ S T) _ _ _ _) s f

end GlobalTheory.SeeSaw.Resc

namespace GlobalTheory.SeeSaw.Resc

end GlobalTheory.SeeSaw.Resc

end
