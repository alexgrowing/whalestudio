import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace DescentAux

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M}

theorem re_cas_le (hSq : SqId) (hE : IsGlRep E) (hU : IsInfUnitary ε E) {L : Fin n → ℝ} {y : M}
    (hy : IsKHWVec ε E L y) : (⟪casimir E y, y⟫_ℂ).re ≤ casValK ε L * ‖y‖ ^ 2 := by
  unfold SqId ForAlg at hSq
  have hd := (hSq n ε M E hE hU y).2.1
  have hnn : 0 ≤ ∑ a : Fin n, ∑ b ∈ Finset.univ.filter (fun b => ε b ≠ ε a), ‖(E a b) y‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by positivity))
  have hK : (⟪casimirK ε E y, y⟫_ℂ).re = casValK ε L * ‖y‖ ^ 2 := by
    rw [casimirK_khwVec ε hE hy, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [casValK]
    left
    norm_cast
  linarith

theorem abs_root_le (a b c : Fin n) : |root a b c| ≤ 1 := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem main (hSq : SqId) (hK : KIrrEx) (hD : Drop) (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (N : Submodule ℂ M) (hN : Stab E N) (μ L : Fin n → ℝ) (R τ s : ℝ) (J : ℕ) (w : ℝ)
    (hR : ∀ y ∈ N, (casValK ε L - R) * ‖y‖ ^ 2 ≤ (⟪casimir E y, y⟫_ℂ).re)
    (hτ : ∀ a b, a < b → τ ≤ μ a - μ b) (hJ : R < J * w)
    (hw : w ≤ 2 * (τ - 2 * (s + J)) - 2 * n - 2) :
    ∀ k : ℕ, k ≤ J → ∀ (L' : Fin n → ℝ), ∀ y ∈ N, y ≠ 0 → KFin ε E y → IsKHWVec ε E L' y →
      (∀ a, |L' a - μ a| ≤ s + ((J : ℝ) - (k : ℝ))) → casValK ε L' ≤ casValK ε L - ((J : ℝ) - (k : ℝ)) * w →
      ∃ (L'' : Fin n → ℝ) (V : Submodule ℂ M), (∀ a, |L'' a - μ a| ≤ s + J) ∧ IsKIrrHW ε E L'' V ∧
        NoDown ε E L'' V := by
  unfold KIrrEx ForAlg at hK
  intro k
  induction k with
  | zero =>
    intro _ L' y hyN hy0 _ hyHW _ hcas
    exfalso
    have h1 := hR y hyN
    have h2 := re_cas_le hSq hE hU hyHW
    have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
    have hc : casValK ε L' ≤ casValK ε L - J * w := by simpa using hcas
    have : casValK ε L - R ≤ casValK ε L' := le_of_mul_le_mul_right (h1.trans h2) hpos
    linarith
  | succ k ih =>
    intro hk L' y hyN hy0 hyK hyHW hbd hcas
    obtain ⟨V, hVN, hIrr⟩ := hK n ε M E hE hU N hN L' y hyN hy0 hyK hyHW
    have hk0 : (0:ℝ) ≤ k := by positivity
    by_cases hND : NoDown ε E L' V
    · refine ⟨L', V, fun a => ?_, hIrr, hND⟩
      have := hbd a
      push_cast at this
      linarith
    · unfold NoDown at hND
      push_neg at hND
      obtain ⟨a, b, hab, _, v, hv, hvHW, hv0⟩ := hND
      apply ih (by omega) (L' - root a b) v
        (layer_le_of_stable hVN (fun c d u hu => hN c d u hu) 1 hv) hv0
        ⟨layer ε E V 1, finiteDimensional_layer hIrr.1 1, layer_kStable hE hIrr.2.1 1, hv⟩ hvHW
      · intro c
        have h1 := abs_le.mp (hbd c)
        have h2 := abs_le.mp (abs_root_le a b c)
        push_cast at h1
        simp only [Pi.sub_apply]
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · have hdrop := hD n ε L' a b hab.ne
        have ha := abs_le.mp (hbd a)
        have hb := abs_le.mp (hbd b)
        have ht := hτ a b hab
        push_cast at ha hb hcas
        nlinarith [ha.1, ha.2, hb.1, hb.2]

end DescentAux

theorem mem_span_of_frobenius_mem_span : SqId → KIrrEx → Drop → Descent := by
  unfold Descent ForAlg
  intro hSq hK hD n ε M _ _ E hE hU N hN μ L R τ s J hR hτ hs hJ y hyN hy0 hyK hyHW
  exact DescentAux.main hSq hK hD hE hU N hN μ L R τ s J _ hR hτ hJ le_rfl J le_rfl L y hyN hy0
    hyK hyHW (fun a => by simpa using hs a) (by simp)

end PositivityTheory.RgHe3
