import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def OnOldBound : Prop :=
  ∀ (k ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (ys : List ℝ) (A : ℝ)
      (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (KB.onOld (PBO.mDiff Bs σ w) ys x e) (K * ‖σ‖ ^ 3 * c)

theorem plusW_length (ys : List ℝ) (w : List C.Letter) : (KB.plusW ys w).length = ys.length + w.length := by
  rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]
  simp

theorem waveDiffForm_of (hO : OnOldBound) : PBO.WaveDiffForm := by
  intro _hP Cb
  obtain ⟨Cs, hCs0, hSQ⟩ := Formalism.FourierDecayAlt.P.PBE.sliceQ
  refine ⟨2 * Cs + 2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut _hInD hχ hε hf hfA hA hcut j hj w hw hwN h hh ys hys hcw
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N₂ : ℕ := 2 * N + 6 with hN₂
  set R : ℝ := ((P.r : ℝ) + 1) ^ 4 with hRdef
  have hR1 : 1 ≤ R := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  set n0 : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn0
  have hn01 : 1 ≤ n0 := by
    have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    rw [hn0]; linarith
  set X : ℝ := ((N + 3 : ℕ) : ℝ) * n0 ^ 2 + n0 ^ 3 with hXdef
  have hX1 : 1 ≤ X := by
    have h1 : 1 ≤ n0 ^ 3 := one_le_pow₀ hn01
    have : 0 ≤ ((N + 3 : ℕ) : ℝ) * n0 ^ 2 := by positivity
    rw [hXdef]; linarith
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * ((N₂ : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - 1 := by
    have hX2 : (N₂ : ℝ) * n0 ^ 2 + n0 ^ 3 ≤ 2 * X := by
      rw [hXdef, hN₂]
      push_cast
      have : 0 ≤ n0 ^ 3 := by positivity
      nlinarith
    have hRX : 1 ≤ R * X := by nlinarith
    have h0 : (2 * Cs + 2) * R * X ≤ A := hA
    calc Cs * R * ((N₂ : ℝ) * n0 ^ 2 + n0 ^ 3) ≤ Cs * R * (2 * X) :=
          mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ = (2 * Cs + 2) * R * X - 2 * (R * X) := by ring
      _ ≤ A - 1 := by linarith
  set MM := 3 * (11 * (N₂ * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hMM
  obtain ⟨bf, hbf⟩ := hfA MM
  have hbf0 : 0 ≤ bf := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) MM f bf := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) MM
  have hψ : ∀ n : ℕ, B.CCle (A - 1) MM (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g)
      (Kp * bf / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, Formalism.FourierDecayAlt.P.PBE.cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) MM (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hbf' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add hf (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  set w' := KB.plusW ys w with hw'
  have hw'len : w'.length ≤ N + 3 := by rw [hw', plusW_length]; omega
  have hN₂w : w'.length ≤ N₂ := by omega
  have hc : P.r - j = P.r - D.ptSize h := by rw [hh.2]
  have hQ := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N₂ P rfl rfl hk2 hχ hA' ε hε j hj w' hN₂w h hc hh e
  choose εa Ka hεa hKa hQ1 _hQ2 using hQ
  set KK : ℝ := ∑ e, Ka e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := fun e =>
    Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun e _ => hKa e
  set cs : ℝ := KK * (bf + Kp * bf) with hcs
  have hcs0 : 0 ≤ cs := by positivity
  have hsl : ∀ n e, B.CCle (P5.Auser P N₂ + 1) (P5.mmUser P N₂) (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs := by
    intro n e
    obtain ⟨-, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
    exact Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKa' e) (by positivity))
  have hxs : ∀ n, KB.slv p.T (D.cutF p.T.base χ (hn n) ε) j hj w' h hh.2 =
      Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) := fun n => rfl
  set mo : ℕ := 5 + (2 * (P.r - j) + P.k + 1) * w'.length with hmo
  obtain ⟨K3, hK30, hK3⟩ := hO P.k (P.r - j) Wp Wq (p.T.bs j) w mo
  set Af : ℝ := P5.Auser P w'.length + 1 with hAf
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' Af le_rfl
  have hq : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) ≤ n0 := by
    rw [hn0]
    have : P.r - j ≤ P.r := Nat.sub_le _ _
    have : ((P.r - j : ℕ) : ℝ) ≤ P.r := by exact_mod_cast this
    push_cast
    linarith
  have hL : (w'.length : ℝ) ≤ (N : ℝ) + 3 := by exact_mod_cast hw'len
  have hdec : Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ) ≤ P5.Auser P N₂ + 1 := by
    have hmo' : ((mo + 1 : ℕ) : ℝ) = 6 + ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) := by
      rw [hmo]; push_cast; ring
    have hnV : ((P5.nV P : ℕ) : ℝ) = n0 := by rw [hn0]; unfold P5.nV; push_cast; ring
    have hR3 : 1 ≤ ((P.r : ℝ) + 1) ^ 3 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
    have hdiff : P5.Auser P N₂ - P5.Auser P w'.length =
        127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by
      unfold P5.Auser; rw [hnV]; ring
    have hgap : (N : ℝ) + 3 ≤ (N₂ : ℝ) - w'.length := by rw [hN₂]; push_cast; linarith
    have hN3 : (3 : ℝ) ≤ (N : ℝ) + 3 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    have h1 : 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ P5.Auser P N₂ - P5.Auser P w'.length := by
      rw [hdiff]
      have hb : n0 ^ 2 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      have hpos : 0 ≤ n0 ^ 2 * ((N : ℝ) + 3) := by positivity
      have hY : 0 ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) := le_trans hpos hb
      have hR : n0 ^ 2 * ((N₂ : ℝ) - w'.length) ≤ ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) :=
        le_mul_of_one_le_left hY hR3
      calc 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ 127 * (((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length))) := by
            linarith
        _ = 127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by ring
    have h2 : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) ≤ n0 * ((N : ℝ) + 3) :=
      mul_le_mul hq hL (Nat.cast_nonneg _) (by linarith)
    have ha3 : 3 ≤ n0 * ((N : ℝ) + 3) := by
      calc (3 : ℝ) ≤ (N : ℝ) + 3 := hN3
        _ = 1 * ((N : ℝ) + 3) := by ring
        _ ≤ n0 * ((N : ℝ) + 3) := mul_le_mul_of_nonneg_right hn01 (by linarith)
    have hb2 : n0 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N : ℝ) + 3) := by
      have e : n0 ^ 2 * ((N : ℝ) + 3) = n0 * (n0 * ((N : ℝ) + 3)) := by ring
      rw [e]
      exact le_mul_of_one_le_left (by linarith) hn01
    have h3 : 3 * (n0 * ((N : ℝ) + 3)) + 17 ≤ 127 * (n0 ^ 2 * ((N : ℝ) + 3)) := by linarith
    rw [hAf, hmo']
    linarith
  have hord : mo ≤ P5.mmUser P N₂ := by
    have h1 : 2 * (P.r - j) + P.k + 1 ≤ P5.nV P := by unfold P5.nV; omega
    have h2 : w'.length ≤ 3 * (P.r + 1) * (N₂ + 2) := by
      have : N + 3 ≤ 3 * (P.r + 1) * (N₂ + 2) := by
        have : 1 ≤ 3 * (P.r + 1) := by omega
        nlinarith
      omega
    have h3 : (2 * (P.r - j) + P.k + 1) * w'.length ≤ P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) :=
      Nat.mul_le_mul h1 h2
    have e : P5.mmUser P N₂ = 5 + 3 * (P.r + 1) * (N₂ + 2) * P5.nV P + N₂ * P.r := rfl
    have e2 : P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) = 3 * (P.r + 1) * (N₂ + 2) * P5.nV P := by ring
    rw [e, hmo]
    rw [e2] at h3
    exact le_trans (Nat.add_le_add_left h3 5) (Nat.le_add_right _ _)
  refine ⟨Cf * (K3 * cs) * (K3 * cs), fun n σ hσ => ?_⟩
  rw [hFn n, hxs n]
  have hx : ∀ e, B.CCle (Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ)) mo (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs :=
    fun e => Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hdec (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hord (hsl n e))
  have hu := hK3 σ hσ ys (Af - 1) _ cs hx
  have hv : ∀ e, B.CCle (Af - 1 - 2 * (w'.length : ℝ)) 5
      (KB.onOld (PBO.mDiff (p.T.bs j) σ w) ys (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n)) e)
      (K3 * ‖σ‖ ^ 3 * cs) := fun e =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ w'.length := Nat.cast_nonneg _; linarith)
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by rw [hmo]; omega) (hu e))
  have hb := hCf _ _ _ _ hu hv
  show ‖D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' _ _‖ ≤ _
  refine hb.trans (le_of_eq ?_)
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
