import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.LastEnt

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem succ_mul_succ_sub_one_div_succ (l t : ℕ) : ((l + 1) * (t + 1) - 1) / (t + 1) = l := by
  have h : (l + 1) * (t + 1) - 1 = t + (t + 1) * l := by rw [Nat.succ_mul]; ring_nf; omega
  rw [h, Nat.add_mul_div_left _ _ (Nat.succ_pos t), Nat.div_eq_of_lt (Nat.lt_succ_self t), zero_add]

theorem eT_zero (τ : D.what₂.Tau) : eT X D pos 0 τ =
    lamAt (X.G.P.lam0 (pos.symm τ).1) (pos.symm τ).2 (Fin.last X.G.P.m) := rfl

theorem eT_succ (l : ℕ) (τ : D.what₂.Tau) : eT X D pos (l + 1) τ =
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 (pos.symm τ).1 s) (fun i => X.Fl.w (pos.symm τ).1 i s) (l + 1))
      (pos.symm τ).2 (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) := rfl

theorem lamAt_last0 (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (X.G.P.lam0 v) s (Fin.last X.G.P.m) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else X.G.P.lam0 v s (Fin.last X.G.P.m) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]

theorem lamAt_lastS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (l + 1)) s
        (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else -(X.Fl.w v (l + 1) s) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
    unfold liftWt
    beta_reduce
    have h1 : 1 ≤ (l + 1) * (X.Fl.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [dif_neg (by simp only [Fin.val_last]; omega)]
    simp only [Fin.val_last]
    have h2 : X.G.P.m + (l + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (l + 1) * (X.Fl.t + 1) - 1 := by omega
    rw [h2, succ_mul_succ_sub_one_div_succ]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]
    unfold liftWt
    beta_reduce
    rw [dif_pos (by simp)]
    rfl

theorem nuv_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨le_refl 1, by omega⟩]
  unfold lamI
  rw [dif_pos ⟨le_refl 1, by omega⟩]
  rfl

theorem nuv_one_at_firstLevelIndex (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v 1 s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last X.G.P.m) + X.w v 1 s := by
  unfold Sys.nuv nu NN
  rw [if_pos ⟨by omega, by omega⟩]
  unfold lamI
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 2
  ext
  simp

theorem nuv_NNS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (l + 1 + 1) s (NN X.G.P.m X.t (l + 1)) = -X.w v (l + 1) s + X.w v (l + 1 + 1) s := by
  have h1 : 1 ≤ (l + 1) * (X.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : (l + 1) * (X.t + 1) + (X.t + 1) = (l + 1 + 1) * (X.t + 1) := by ring
  unfold Sys.nuv nu
  rw [if_neg (by unfold NN; omega), if_pos ⟨by unfold NN; omega, by unfold NN; omega⟩]
  have h2 : NN X.G.P.m X.t (l + 1) - (X.G.P.m + 2) = (l + 1) * (X.t + 1) - 1 := by unfold NN; omega
  rw [h2, succ_mul_succ_sub_one_div_succ]

end GlobalTheory.TwV.DelA.LastEnt

open GlobalTheory.TwV.DelA.LastEnt in

theorem GlobalTheory.TwV.DelA.eT_last_pair : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  intro p _ X D pos j τ
  have hc1 : cT1 X D pos j τ = X.G.P.lam0 (pos.symm τ).1 (pos.symm τ).2 0 + wT X D pos j τ :=
    nuv_one X j (pos.symm τ).1 (pos.symm τ).2
  have hw : wT X D pos j τ = X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2 := rfl
  rw [hc1, eT_succ X D pos j τ, lamAt_lastS X j]
  cases j with
  | zero =>
    rw [eT_zero, lamAt_last0, nuv_one_at_firstLevelIndex, hw]
    constructor <;> split_ifs <;> ring
  | succ l =>
    rw [eT_succ X D pos l τ, lamAt_lastS X l, nuv_NNS, hw]
    constructor <;> split_ifs <;> ring
