import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def ThickSetDensity : Prop := L.sc.x ^ (-L.sc.eps) ≤ (D.host.T2.card : ℝ) / D.R.n

variable {L}

def ChBadp_at (X : G.Inst D L) : Prop :=
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

variable (L)

open Classical in

def cands (K : G.Consts) : Finset ℕ := (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => G.Cand D L K p)

variable {L}

open Classical in

def ChW_at (X : G.Inst D L) (K : G.Consts) : Prop :=
  ∑ p ∈ cands L K, Real.log p / p *
      ((if L.sc.x ^ (-L.sc.eps) < G.Sig X K (G.aL L) (G.bL L) p then 2 else 0) +
        4 * G.Sig X K (G.aL L) (G.bL L) p) ≤ L.sc.x ^ (-9 : ℝ)

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ThickSetDensityEventually : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ThickSetDensity (Fm.L x i)
def ChosenBadp : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChBadp_at (Fm.Gx x i)

def ChosenW : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → ChW_at (Fm.Gx x i) Fm.GK

def ChosenWS : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    (∃ i1 : Fm.Ix x, ∀ t : (Fm.D x i1).host.TT,
        (Fm.L x i1).aT t = av (t : (Fm.D x i1).R.A).val ∧
        (Fm.L x i1).bT t = bv (t : (Fm.D x i1).R.A).val) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → ChW_at (Fm.Gx x i) Fm.GK

def Chosen7 (CH C0 C5 c6 : ℝ) : Prop :=
  ThickSetDensityEventually Fm ∧ ChosenTT Fm ∧ ChosenBadp Fm ∧ ChosenWS Fm ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def WeightVectorSmallSharesSeven (C0 CH : ℝ) : Prop := ∃ C5 c6 : ℝ, 0 < C5 ∧ 0 < c6 ∧ Chosen7 Fm CH C0 C5 c6

theorem chosenWS_of_cover (hW : ChosenW Fm) (hc : Fm.CoverAll) : ChosenWS Fm := by
  obtain ⟨x0, hx0⟩ := hW
  refine ⟨max x0 (Fm.x1 + 1), fun x hx hxW => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_max_right x0 (Fm.x1 + 1)
    linarith
  obtain ⟨i0, av, bv, hwin, hall⟩ := hx0 x hxa hxW
  have hu : (Fm.D x i0).host.u0.val < (Fm.D x i0).R.n := by
    first
      | exact (Fm.D x i0).host.u0.isLt
      | exact ZMod.val_lt _
  obtain ⟨i1, -, hi1⟩ := hc x hx1 i0 _ av bv hu hwin
  exact ⟨i0, av, bv, hwin, ⟨i1, hi1⟩, hall⟩

end Family

end Formalism.MainNotions

end
