import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem room_neg_log_epStar (f d L M k0 S : ℝ) (hf : 1 ≤ f) (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hM : 0 < M) (hk : 0 < k0) (hS : 1 ≤ S)
    (h : Real.log (M * k0) ≤ 19 * L + 3 + Real.log d) :
    0 < epStar M f S k0 ∧ epStar M f S k0 ≤ 1 ∧
      -Real.log (epStar M f S k0) ≤ 19 * L + 6 + Real.log d + f + Real.log S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hfS : 1 ≤ f * S := one_le_mul_of_one_le_of_one_le hf hS
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hpi := Real.pi_gt_three
  have hD : 0 < M * (f * S + 2) * k0 * Real.log 2 := by positivity
  unfold epStar
  refine ⟨lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rcases min_choice 1 (Real.pi / (M * (f * S + 2) * k0 * Real.log 2)) with h1 | h1 <;> rw [h1]
  · rw [Real.log_one]; linarith
  · have hMk : 0 < M * k0 := by positivity
    have e : M * (f * S + 2) * k0 * Real.log 2 = (M * k0) * ((f * S + 2) * Real.log 2) := by ring
    rw [Real.log_div (by positivity) hD.ne', e, Real.log_mul hMk.ne' (by positivity)]
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
    have h3 : Real.log ((f * S + 2) * Real.log 2) ≤ Real.log (3 * f * S) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h6 : Real.log (3 * f * S) = Real.log 3 + Real.log f + Real.log S := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by positivity)
    linarith

theorem room_log_radius (f r : ℕ) (d e S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (he : 0 < e) (hS : 1 ≤ S) :
    0 < 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5)) =
      Real.log (1600 / 3) + Real.log r + (1 / 2) * Real.log f + (1 / 2) * Real.log S
        + 3 * Real.log ((f : ℝ) * r) + Real.log d - (1 / 2) * Real.log e := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hS' : (0 : ℝ) < S := by linarith
  have hd' : (0 : ℝ) < d := by linarith
  have h1 : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.2 hf'
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have h4 : 0 < Real.sqrt (S * r) := Real.sqrt_pos.2 (by positivity)
  have E : 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) =
      1600 / 3 * Real.sqrt r * Real.sqrt f * Real.sqrt (S * r) * ((f : ℝ) * r) ^ 3 * d / Real.sqrt e := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR d5mu frameRadius
    field_simp
    norm_num
  rw [E]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) hd'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) h4.ne',
    Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_pow, Real.log_sqrt he.le, Real.log_sqrt hf'.le, Real.log_sqrt hr'.le,
    Real.log_sqrt (by positivity), Real.log_mul hS'.ne' hr'.ne']
  push_cast
  ring

theorem room_of_constants : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  refine ⟨3000, by norm_num, ?_⟩
  intro f r p0 d L Om M k0 S hf hr hp hd hL hM hk hS h
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp' : (p0 : ℝ) ≤ r := by exact_mod_cast hp
  obtain ⟨he0, he1, he2⟩ := room_neg_log_epStar f d L M k0 S hf' hd hL hM hk hS h
  obtain ⟨hX0, hX⟩ := room_log_radius f r d _ S hf hr hd he0 hS
  unfold frameBasisRadius
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt (epStar M f S k0) / Real.sqrt f))
    (3 * frameRadius S r / 5) with hXdef
  clear_value X
  have hle : Real.log (epStar M f S k0) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (f : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have hfn : (f : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_right (by linarith) hr'
  have hrn : (r : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_left (by linarith) hf'
  have a1 : 0 ≤ Real.log d := Real.log_nonneg hd
  have a2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have a3 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((f : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have b3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by linarith)
  have b4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < r by linarith)
  have b5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (f : ℝ) * r by linarith)
  have b6 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1600 / 3 by norm_num)
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  have hX1' : 1 ≤ X := by
    by_contra hc
    have := Real.log_neg hX0 (not_le.1 hc)
    linarith
  refine ⟨one_le_pow₀ hX1', ?_⟩
  intro s t hs ht hst C A hC hA
  have hOm := abs_nonneg Om
  set Z : ℝ := (f : ℝ) * r + L + Real.log d + |Om| with hZ
  have hZn : (f : ℝ) * r ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hXZ : Real.log X ≤ 600 * Z + Real.log S := by rw [hX]; linarith
  have hXZ' : Real.log X ≤ 600 * (Z * (1 + Real.log S)) := by
    have : Real.log S ≤ Z * Real.log S := le_mul_of_one_le_left a2 hZ1
    linarith
  have hpd : Formalism.L2.LamCM.pDeg Om ≤ Z := by unfold Formalism.L2.LamCM.pDeg; linarith
  have hlog : Real.log (X ^ (2 * p0 + 1)) ≤ 1800 * (Z ^ 2 * (1 + Real.log S)) := by
    rw [Real.log_pow]
    push_cast
    calc (2 * (p0 : ℝ) + 1) * Real.log X ≤ (3 * Z) * (600 * (Z * (1 + Real.log S))) :=
          mul_le_mul (by linarith) hXZ' hX1 (by linarith)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.log (X ^ (2 * p0 + 1)) := Real.log_nonneg (one_le_pow₀ hX1')
  rw [Real.log_mul (by positivity) (by positivity)]
  have hZW : Z ≤ Z ^ 2 * (1 + Real.log S) :=
    (le_self_pow₀ hZ1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hZA : Z ^ 2 ≤ Z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hZ1 hA
    rwa [Real.rpow_two] at this
  set W := Z ^ 2 * (1 + Real.log S) with hW
  set Y := Real.log (X ^ (2 * p0 + 1)) with hY
  have hW0 : 0 ≤ W := by linarith
  have c1 : (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Y) * (s + t) ≤ (901 * W) * S :=
    mul_le_mul (by linarith) hst (by linarith) (by linarith)
  have c2 : s * (Real.log r + Y) ≤ S * (1801 * W) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c3 : 3000 * W ≤ C * Z ^ A * (1 + Real.log S) := by
    have : 3000 * Z ^ 2 ≤ C * Z ^ A := mul_le_mul hC hZA (by positivity) (by linarith)
    calc 3000 * W = (3000 * Z ^ 2) * (1 + Real.log S) := by rw [hW]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by linarith)
  have c4 : 3000 * W * S ≤ C * Z ^ A * (1 + Real.log S) * S :=
    mul_le_mul_of_nonneg_right c3 (by linarith)
  have c5 : 0 ≤ W * S := mul_nonneg hW0 (by linarith)
  linarith

end GlobalTheory
