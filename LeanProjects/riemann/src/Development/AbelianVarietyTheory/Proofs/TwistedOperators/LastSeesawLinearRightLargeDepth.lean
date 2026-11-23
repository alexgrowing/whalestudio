import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastLinR

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem castSch_lin {V : HSp D} {n n' : ℕ} (e : n = n') (c : ℂ) (f g : WO V (G.V (.grid D.R.m n)) → ℂ) :
    castSch G e (c • f + g) = c • castSch G e f + castSch G e g := by
  subst e; rfl

theorem lastDat_lin (Wl : G.Weil) {t : T} {M : Vol G} (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (c : ℂ) (Φ₂ Φ₂' : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat Wl hM j hj vN g Φ₁ (c • Φ₂ + Φ₂') u v = c * lastDat Wl hM j hj vN g Φ₁ Φ₂ u v + lastDat Wl hM j hj vN g Φ₁ Φ₂' u v := by
  simp only [lastDat, GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.LastLinR

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem lastLin_one (ch : Choice R) : LastLin ch 1 := by
  intro j hj hjm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  have h0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hlt : j + 1 < D.R.m := by omega
  obtain rfl : a = ⟨j + 1, hlt⟩ := Fin.ext ha
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hlt⟩ := fun e => by simp [Fin.ext_iff] at e
  unfold conAt
  rw [dif_pos h0, dif_pos h0, dif_pos h0]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  have hlin : ch.W.fock (.mu t D.R.m (j + 1)) (c • φ + φ') (P ⟨j + 1, hlt⟩) =
      c • ch.W.fock (.mu t D.R.m (j + 1)) φ (P ⟨j + 1, hlt⟩) + ch.W.fock (.mu t D.R.m (j + 1)) φ' (P ⟨j + 1, hlt⟩) := by
    simp only [GridData.Weil.fock]
    exact GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ ch.W.ψ_std ch.W.θ_is _ _ _ _ c hφ hφ' _
  rw [hlin, GlobalTheory.LastLinR.castSch_lin, GlobalTheory.LastLinR.lastDat_lin]

end

theorem big_lastLin_one : Big fun ch => LastLin ch 1 :=
  by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  exact lastLin_one ch

end GlobalTheory.ConnectionLinear
