import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKFIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndDecInfAndKFinSmooth
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GlobalTheory.NoPr.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.ThreeDimData

theorem aOf_mono (r : ℕ) {h h' : ℝ} (hh : h ≤ h') : aOf r h ≤ aOf r h' := by
  unfold aOf
  exact div_le_div_of_nonneg_right hh (by positivity)

theorem gapOK_mono {k r : ℕ} {h h' : ℝ} (hh : h ≤ h') (H : GapOK k r h) : GapOK k r h' :=
  ⟨H.1, H.2.1.trans hh, H.2.2.1.trans (aOf_mono r hh), H.2.2.2.trans (aOf_mono r hh)⟩

theorem exists_gapOK (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, GapOK k r h := by
  set c : ℝ := 8 * Real.sqrt (2 * ((r : ℝ) + 1)) with hc
  have hc0 : 0 < c := by positivity
  set A : ℝ := 2 * Mexp r * (AS k r + AG k r) + AG k r + 3
  set B : ℝ := 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3
  refine ⟨max (120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) (max (A * c) (B * c)), hk, le_max_left _ _, ?_, ?_⟩
  · show A ≤ _ / c
    rw [le_div_iff₀ hc0]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · show B ≤ _ / c
    rw [le_div_iff₀ hc0]
    exact (le_max_right _ _).trans (le_max_right _ _)

theorem exists_gp (k r : ℕ) (hk : 1 ≤ k) (ε : Fin (2 * r + k + 1) → Bool) :
    ∃ mu : Fin (2 * r + k + 1) → ℝ, IsHCParam mu ∧ Gp k r ε mu := by
  obtain ⟨h, hh⟩ := exists_gapOK k r hk
  obtain ⟨N, hN⟩ := exists_nat_ge h
  refine ⟨fun a => (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 - ((N : ℝ) + 1) * ((a : ℕ) : ℝ), ⟨?_, ?_⟩, h, ?_, hh⟩
  · intro a b hab
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have := mul_lt_mul_of_pos_left this hN0
    simp only
    linarith
  · intro a
    refine ⟨-(((N : ℤ) + 1) * ((a : ℕ) : ℤ)), ?_⟩
    simp only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one]
    ring
  · intro a b hab
    have hne : (a : ℕ) ≠ (b : ℕ) := fun e => hab (by rw [Fin.ext e])
    have h1 : (1 : ℝ) ≤ |((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)| := by
      have : (1 : ℤ) ≤ |((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)| := Int.one_le_abs (by omega)
      exact_mod_cast this
    have e : (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 - ((N : ℝ) + 1) * ((a : ℕ) : ℝ) -
        ((((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 - ((N : ℝ) + 1) * ((b : ℕ) : ℝ)) =
        ((N : ℝ) + 1) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by ring
    simp only
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith

theorem gp_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} (H : Gp k r ε mu) :
    1 ≤ k ∧ ∀ a b, ε a ≠ ε b → 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ |mu a - mu b| := by
  obtain ⟨h, h1, h2⟩ := H
  exact ⟨h2.1, fun a b hab => h2.2.1.trans (h1 a b hab)⟩

theorem not_gp_small : ¬ Gp 1 0 (fun i => decide (i = 0)) (fun i => if i = 0 then 1 / 2 else -1 / 2) := by
  intro H
  have := (gp_gap H).2 0 1 (by decide)
  have h10 : (1 : Fin (2 * 0 + 1 + 1)) ≠ 0 := by decide
  simp only [if_true, if_neg h10] at this
  norm_num at this

theorem not_gp_zero (r : ℕ) (ε : Fin (2 * r + 0 + 1) → Bool) (mu : Fin (2 * r + 0 + 1) → ℝ) : ¬ Gp 0 r ε mu :=
  fun H => absurd (gp_gap H).1 (by decide)

theorem gp_of_onePlace {k r : ℕ} {L : LocBessel k r} {h : ℝ} {μG : Measure (Mt k r)} {w0 : L.Hs} {l : L.Hs → L.Wp}
    {l' : L.Hs → L.Wq} (H : GlobalTheory.CellAmp.OnePlaceKF L h μG w0 l l') : Gp k r L.ε L.lam := ⟨h, H.1.1, H.1.2.1⟩

theorem ampKF0_iff_gapIn : AmpKF0 ↔ GlobalTheory.GapIn.AmpKF0 := Iff.rfl

open Formalism.MainNotions.S.Pv.AmpDDPf in

theorem ampKF0_holds : AmpKF0 := by
  intro k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance
  have hIn := GlobalTheory.DecInputs.decLow_and_decInf_and_kFinSmooth
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end GlobalTheory.NoPr.Model

end
