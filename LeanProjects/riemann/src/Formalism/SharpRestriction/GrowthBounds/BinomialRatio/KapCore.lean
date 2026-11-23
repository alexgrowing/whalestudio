import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem kap_core {p k N N1 La Q c a b' Y CE1 CE2 Cm : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hN1 : 1 ≤ N1)
    (_hLa : 0 ≤ La) (hQ : 1 ≤ Q) (hc : 0 ≤ c) (hb : 0 < b') (hp : k ^ 2 * Y ^ 2 ≤ p)
    (hLaNY : 8 * Real.log (N * Y) ≤ La) (hLak : La ≤ k) (hkb : k * b' ≤ a) (hLaY : La * Y * b' ≤ a)
    (hHc : k ^ 3 * Q ^ 2 * c * Y ≤ b') (hHb : k ^ 3 * Q * Y ≤ b') (h1 : 0 ≤ CE1) (h2 : 0 ≤ CE2) (h3 : 0 ≤ Cm) :
    Real.exp (-La / 8) + k * Q * (m0G4 Cm k N1 Q c + N1 * k) / b' + 1 / Y +
        k * errorTermBound CE1 CE2 p k N1 Q c a b' La / a ≤ (Cm + 4 * CE1 + CE2 + 15) * (N1 / Y) := by
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  have hN10 : 0 < N1 := by linarith
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hk0 hb) hkb
  have hba : b' ≤ a := le_trans (le_mul_of_one_le_left hb.le hk) hkb
  have hkY : k * Y ≤ p := by
    refine le_trans ?_ hp
    exact mul_le_mul (le_self_pow₀ hk two_ne_zero) (le_self_pow₀ hY two_ne_zero) hY0.le (by positivity)
  have hp1 : 1 ≤ p := le_trans (one_le_mul_of_one_le_of_one_le hk hY) hkY
  have hp0 : 0 < p := by linarith
  have hpp : p ≤ p ^ 2 := le_self_pow₀ hp1 two_ne_zero
  have hYp : Y ≤ p := le_trans (le_mul_of_one_le_left hY0.le hk) hkY
  have y1 : 1 / Y ≤ N1 / Y := div_le_div_of_nonneg_right hN1 hY0.le
  have t1 : Real.exp (-La / 8) ≤ N1 / Y := by
    have e : Real.exp (-La / 8) ≤ Real.exp (-(Real.log (N * Y))) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity)] at e
    have : (N * Y)⁻¹ ≤ 1 / Y := by
      rw [one_div]; exact inv_anti₀ hY0 (le_mul_of_one_le_left hY0.le hN)
    linarith
  obtain ⟨β, hβ⟩ : ∃ β, β = b' / Y := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have c1 : k ^ 3 * Q ^ 2 * c ≤ β := by rw [hβ, le_div_iff₀ hY0]; exact hHc
  have c2 : k ^ 3 * Q ≤ β := by rw [hβ, le_div_iff₀ hY0]; exact hHb
  have k23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
  have k13 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have Q12 : Q ≤ Q ^ 2 := le_self_pow₀ hQ two_ne_zero
  have d1 : k ^ 2 * Q ^ 2 * c ≤ β :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k23 (by positivity)) hc) c1
  have d2 : k * Q * c ≤ β :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul k13 Q12 hQ0.le (by positivity)) hc) c1
  have d3 : k ^ 2 * Q ≤ β := le_trans (mul_le_mul_of_nonneg_right k23 hQ0.le) c2
  have t2 : k * Q * (m0G4 Cm k N1 Q c + N1 * k) / b' ≤ (Cm + 13) * (N1 / Y) := by
    rw [div_le_iff₀ hb]
    have e1 : (Cm + 13) * (N1 / Y) * b' = (Cm + 13) * N1 * β := by rw [hβ]; ring
    have e2 : k * Q * (m0G4 Cm k N1 Q c + N1 * k) =
        Cm * N1 * (k ^ 2 * Q ^ 2 * c) + 12 * (k * Q * c) + N1 * (k ^ 2 * Q) := by unfold m0G4 m1G4; ring
    rw [e1, e2]
    have f1 : Cm * N1 * (k ^ 2 * Q ^ 2 * c) ≤ Cm * N1 * β := mul_le_mul_of_nonneg_left d1 (by positivity)
    have f3 : N1 * (k ^ 2 * Q) ≤ N1 * β := mul_le_mul_of_nonneg_left d3 hN10.le
    have f2 : β ≤ N1 * β := le_mul_of_one_le_left hβ0.le hN1
    linarith
  obtain ⟨α, hα⟩ : ∃ α, α = a / Y := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβα : β ≤ α := by rw [hβ, hα]; exact div_le_div_of_nonneg_right hba hY0.le
  have g1 : k * (a / p ^ 2) ≤ α := by
    rw [← mul_div_assoc, hα, div_le_div_iff₀ (by positivity) hY0]
    calc k * a * Y = a * (k * Y) := by ring
      _ ≤ a * p ^ 2 := mul_le_mul_of_nonneg_left (le_trans hkY hpp) ha.le
  have g2 : k * (b' / p) ≤ α := by
    rw [← mul_div_assoc, hα, div_le_div_iff₀ hp0 hY0]
    exact mul_le_mul hkb hYp hY0.le ha.le
  have g3 : k * (La * N1 * a / (p * k)) ≤ N1 * α := by
    have e : k * (La * N1 * a / (p * k)) = La * N1 * a / p := by field_simp
    rw [e, hα, ← mul_div_assoc, div_le_div_iff₀ hp0 hY0]
    calc La * N1 * a * Y = N1 * a * (La * Y) := by ring
      _ ≤ N1 * a * p :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hLak hY0.le) hkY) (by positivity)
  have g4 : k * (La * b' / k) ≤ α := by
    have e : k * (La * b' / k) = La * b' := by field_simp
    rw [e, hα, le_div_iff₀ hY0]
    linarith [hLaY]
  have g5 : k * (k ^ 2 * N1 * Q ^ 2 * c) ≤ N1 * α := by
    have e : k * (k ^ 2 * N1 * Q ^ 2 * c) = N1 * (k ^ 3 * Q ^ 2 * c) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (le_trans c1 hβα) hN10.le
  have t4 : k * errorTermBound CE1 CE2 p k N1 Q c a b' La / a ≤ (4 * CE1 + CE2) * (N1 / Y) := by
    rw [div_le_iff₀ ha]
    have e1 : (4 * CE1 + CE2) * (N1 / Y) * a = (4 * CE1 + CE2) * (N1 * α) := by rw [hα]; ring
    have e2 : k * errorTermBound CE1 CE2 p k N1 Q c a b' La =
        CE1 * (k * (a / p ^ 2) + k * (b' / p) + k * (La * N1 * a / (p * k)) + k * (La * b' / k)) +
          CE2 * (k * (k ^ 2 * N1 * Q ^ 2 * c)) := by unfold errorTermBound; ring
    rw [e1, e2]
    have f0 : α ≤ N1 * α := le_mul_of_one_le_left hα0.le hN1
    have f1 : CE1 * (k * (a / p ^ 2) + k * (b' / p) + k * (La * N1 * a / (p * k)) + k * (La * b' / k)) ≤
        CE1 * (4 * (N1 * α)) := mul_le_mul_of_nonneg_left (by linarith) h1
    have f2 : CE2 * (k * (k ^ 2 * N1 * Q ^ 2 * c)) ≤ CE2 * (N1 * α) := mul_le_mul_of_nonneg_left g5 h2
    linarith
  linarith

theorem rest2 (D : Formalism.BasicNotions.D7) : FamilyFourthBound D := by
  apply TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hCc hC0 _ h1 h2 h3 _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 Ckap hCkap
  refine ⟨Ckap * (Cm + 4 * CE1 + CE2 + 15), by positivity, ?_⟩
  intro X hD hI hc
  have S := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  have hk5 := S.k5
  have hN2 := S.N2
  have hLaY : X.La C0 * X.Y * X.b' ≤ X.a := by
    refine le_trans ?_ S.kYLab
    have hY0 : 0 < X.Y := by have := S.Y1; linarith
    have hLa0 : 0 < X.La C0 := by have := S.La1; linarith
    have hb := S.bpos
    have : 1 * (X.Y * X.La C0 * X.b') ≤ X.k * (X.Y * X.La C0 * X.b') :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [this]
  have core := kap_core (p := X.p) (k := X.k) (N := X.N) (N1 := X.N1) (La := X.La C0) (Q := X.Q) (c := X.c)
    (a := X.a) (b' := X.b') (Y := X.Y) (CE1 := CE1) (CE2 := CE2) (Cm := Cm) (by linarith) S.Y1 (by linarith) S.one_le_level_alt
    (by have := S.La1; linarith) S.Q1 (by positivity) S.bpos S.pk S.LaNY S.LaLeK S.kb hLaY
    (by have := S.Hc2 zero_le_one; linarith) (by have := S.Hb1 zero_le_one; linarith)
    (by linarith) (by linarith) (by linarith)
  have hN0 : 0 ≤ X.N := by linarith
  calc X.kapP C0 CE1 CE2 Cm Ckap
      = Ckap * X.N * (Real.exp (-X.La C0 / 8) + X.k * X.Q * (m0G4 Cm X.k X.N1 X.Q X.c + X.N1 * X.k) / X.b' + 1 / X.Y +
        X.k * errorTermBound CE1 CE2 X.p X.k X.N1 X.Q X.c X.a X.b' (X.La C0) / X.a) := rfl
    _ ≤ Ckap * X.N * ((Cm + 4 * CE1 + CE2 + 15) * (X.N1 / X.Y)) :=
        mul_le_mul_of_nonneg_left core (by positivity)
    _ = Ckap * (Cm + 4 * CE1 + CE2 + 15) * X.N * X.N1 / X.Y := by ring

end Formalism.MainNotions.ColumnSystems.Pf
