import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.IoExist
import Formalism.LocalToGlobal.IndefiniteReal.MultGood
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Links Formalism.IndefR.Mult Finset

namespace Formalism.IndefR.Fock.KV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem tauE_injective {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

theorem tauE_ne_conj (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem sig_Wc (i : Fin D.R.m) (τ : D.what₂.Tau) : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
  D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _

end Formalism.IndefR.Fock.KV

end
