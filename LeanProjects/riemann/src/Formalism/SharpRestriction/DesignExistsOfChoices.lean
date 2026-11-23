import Formalism.SharpRestriction.MuTuOfTuSize
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def MinkDiv : Prop := ∀ n : ℕ, MinkMult n (minkM n)

def DGamDvdF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
    ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)

def CodeUpF {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    (Fintype.card (Fm.D x i).what₂.Word : ℝ) ≤ C0 * GamOf (Fm.L x i) ^ 2 * x ^ CH + 1

def DesignChoices (𝒞 : FamClass) (C0 : ℝ) (cT : ℝ → ℝ → ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH C5 Cb : ℝ),
    𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ 0 < C5 ∧ 0 < Cb ∧ ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧
      ChosenCode Fm C0 CH ∧ BoxesF Fm ∧ QDRowsF Fm ∧ DGamDvdF Fm ∧ cT eps Fm.CYL ≤ Fm.CTu ∧
      TameDistinctF Fm ∧ Fm.CF = CH ∧ CodeUpF Fm C0 CH ∧ Fm.CYL ≤ 9

theorem log_minkM_fN (R : Ranks) :
    Real.log (minkM (2 * R.f * R.N R.m) : ℝ) ≤ 12 * R.f * R.N R.m * Real.log ((R.f : ℝ) * R.N R.m) := by
  have hy : (2 : ℝ) ≤ (R.f : ℝ) * R.N R.m := by exact_mod_cast R.two_le_fN
  have h1 := log_minkM_le_two (2 * R.f * R.N R.m)
  have e : ((2 * R.f * R.N R.m : ℕ) : ℝ) = 2 * ((R.f : ℝ) * R.N R.m) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((R.f : ℝ) * R.N R.m)) = 2 * 2 * ((R.f : ℝ) * R.N R.m) := by ring
  have h2 : Real.log (2 * (2 * ((R.f : ℝ) * R.N R.m))) =
      Real.log 2 + Real.log 2 + Real.log ((R.f : ℝ) * R.N R.m) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((R.f : ℝ) * R.N R.m) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((R.f : ℝ) * R.N R.m)) * (Real.log 2 + Real.log 2 + Real.log ((R.f : ℝ) * R.N R.m)) ≤
      2 * (2 * ((R.f : ℝ) * R.N R.m)) * (3 * Real.log ((R.f : ℝ) * R.N R.m)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc _ ≤ 2 * (2 * ((R.f : ℝ) * R.N R.m)) * (3 * Real.log ((R.f : ℝ) * R.N R.m)) := h1.trans h4
    _ = _ := by ring

theorem dGamSize_of_dvd {eps : ℝ} (Fm : FamP eps) (h : DGamDvdF Fm) : DGamSize Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨12, x0, fun x hx i u => le_trans ?_ (log_minkM_fN _)⟩
  have hp := minkM_pos (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)
  have hd := h x hx i u
  have h0 : 0 < ((Fm.D x i).mem u).C.DGam := Nat.pos_of_dvd_of_pos hd hp
  exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.le_of_dvd hp hd)

theorem designExists_of_choices {𝒞 : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (hEx : DesignChoices 𝒞 C0 cT)
    (hTu : Closed 𝒞 fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hProv : Closed 𝒞 fun Fm _ => ChosenProviso Fm C0)
    (hThin : Closed 𝒞 fun Fm _ => BoxesF Fm → QDRowsF Fm → (∃ C5 : ℝ, 0 < C5 ∧ ChosenQD Fm C5) →
      ∃ c6 : ℝ, 0 < c6 ∧ ChosenThin Fm c6) : DesignExists 𝒞 C0 := by
  obtain ⟨ε0, h0, hEx⟩ := hEx
  obtain ⟨ε1, h1, hA⟩ := hTu.and (hProv.and hThin)
  refine ⟨min ε0 ε1, lt_min h0 h1, fun e he hle K => ?_⟩
  obtain ⟨K', hK'⟩ := hA e he (hle.trans (min_le_right _ _))
  obtain ⟨Fm, CH, C5, Cb, hc, hCH, hL, h5, hb, a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ :=
    hEx e he (hle.trans (min_le_left _ _)) (K.sup K')
  obtain ⟨hL1, hL2⟩ := (Fm.large_sup K K' CH).1 hL
  obtain ⟨b1, b2, b3⟩ := hK' Fm CH hc hL2
  obtain ⟨c6, h6, b3⟩ := b3 a6 a7 ⟨C5, h5, a4⟩
  exact ⟨Fm, CH, hc, hCH, hL1, ⟨C5, c6, Cb, h5, h6, hb, a1, a2, a3, a4, b3, b2, a5⟩, b1 a9, dGamSize_of_dvd Fm a8⟩

end Formalism.MainNotions

end
