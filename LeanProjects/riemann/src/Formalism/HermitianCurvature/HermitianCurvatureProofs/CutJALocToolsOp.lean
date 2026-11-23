import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section op

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem coefLeib {O UU : Set (B.Mat k r)} (hO : IsOpen O) (hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ UU)
    {a : B.Mat k r → (E →L[ℂ] E')} {Φ : B.Mat k r → E} {d Bg A : ℝ} (hBg : 0 ≤ Bg)
    (ha : B.CkOn ⊤ UU a)
    (hab : ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O → ‖B.dLR u v a g‖ ≤ C * B.gN g ^ (d + Bg * m))
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ)
    (hz : ∀ g ∈ B.GV k r, g ∈ O → Φ g = 0) :
    B.CkOn ⊤ (B.GV k r) (ap a Φ) ∧ ∀ n : ℕ, B.InCC (A - d - Bg * n) n (ap a Φ) := by
  have hP : Pr O UU ⊤ a Φ := ⟨ha, hΦ, hz⟩
  refine ⟨hP.ck hO hcov, fun n => ?_⟩
  choose Ca hCa using hab
  choose cF hcF using hΦg
  set Ka : ℝ := ∑ j ∈ Finset.range (n + 1), |Ca j| with hKa
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKaj : ∀ j ≤ n, |Ca j| ≤ Ka := fun j hj =>
    Finset.single_le_sum (f := fun j => |Ca j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hKa0 : 0 ≤ Ka := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCK : 0 ≤ Ka * K := mul_nonneg hKa0 hK0
  refine ⟨2 ^ n * (Ka * K), sCkOn_mono le_top (hP.ck hO hcov), fun u v hu hv hl g hg => ?_⟩
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hP' : Pr O UU ((wL u ++ wR v).length : ℕ) a Φ := hP.mono le_top
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hP'.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hCK
  · have hb := leib_bound hO hcov g hg (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))
      (wL u ++ wR v) a Φ hlie hP' (by
        intro w₁ w₂ hs₁ hs₂ hl₁₂
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
        rw [len_LR, len_LR] at hl₁₂
        have hl₁ : u₁.length + v₁.length ≤ n := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ n := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
        have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
        have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
        have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
        set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
        set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
        have b1 : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Ka * B.gN g ^ (d + Bg * L₁) := by
          rw [← dLR_eq]
          have h1 := hCa (u₁.length + v₁.length) u₁ v₁ hu₁' hv₁' le_rfl g hg hgO
          calc _ ≤ Ca (u₁.length + v₁.length) * B.gN g ^ (d + Bg * L₁) := by rw [hL₁]; exact h1
            _ ≤ |Ca (u₁.length + v₁.length)| * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
            _ ≤ Ka * B.gN g ^ (d + Bg * L₁) :=
              mul_le_mul_of_nonneg_right (hKaj _ hl₁) (Real.rpow_nonneg hp.le _)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Φ g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
          rw [← dLR_eq]
          have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
          have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
            rw [← Real.rpow_add hp]; simp
          have h4 : ‖B.dLR u₂ v₂ Φ g‖ =
              B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖) := by
            rw [← mul_assoc, e, one_mul]
          rw [h4]
          have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ Φ g‖ ≤ K := by
            refine le_trans ?_ (hKj _ hl₂)
            refine le_trans ?_ (le_abs_self _)
            simpa [hL₂] using h1
          calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
            _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
        have hsum : (d + Bg * L₁) + (Bg * L₂ - A) = d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
          rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
        calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) Φ g‖
            ≤ (Ka * B.gN g ^ (d + Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
              mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hKa0 (Real.rpow_nonneg hp.le _))
          _ = Ka * K * (B.gN g ^ (d + Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
          _ = Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
              rw [← Real.rpow_add hp, hsum])
    have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
    have e2 : B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
      rw [← Real.rpow_add hp]
      refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
      have h6 : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
      nlinarith [mul_le_mul_of_nonneg_left h6 hBg]
    have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
    calc B.gN g ^ (A - d - Bg * n) * ‖Dw (wL u ++ wR v) (ap a Φ) g‖
        ≤ B.gN g ^ (A - d - Bg * n) * (2 ^ (wL u ++ wR v).length *
            (Ka * K * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
      _ = 2 ^ (wL u ++ wR v).length * (Ka * K) *
            (B.gN g ^ (A - d - Bg * n) * B.gN g ^ (d + Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
      _ ≤ 2 ^ (wL u ++ wR v).length * (Ka * K) * 1 :=
          mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
      _ ≤ 2 ^ n * (Ka * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem rwG {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) {Φ : B.Mat k r → E} {A Bg : ℝ}
    (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (hΦg : ∀ m : ℕ, B.InCC (A - Bg * m) m Φ) :
    B.CkOn ⊤ (B.GV k r) (B.Rw w Φ) ∧ ∀ m : ℕ, B.InCC (A - Bg * w.length - Bg * m) m (B.Rw w Φ) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hw x (by simpa [wL] using hx))
    simpa using hΦ
  · have h := InCC_Rw (m := m) hw (hΦg (m + w.length))
    have e : A - Bg * ((m + w.length : ℕ) : ℝ) = A - Bg * w.length - Bg * m := by push_cast; ring
    rwa [e] at h

theorem listSumG {ι : Type*} (l : List ι) (f : ι → B.Mat k r → E) {A Bg : ℝ}
    (h : ∀ i ∈ l, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (A - Bg * m) m (f i)) :
    B.CkOn ⊤ (B.GV k r) (fun g => (l.map fun i => f i g).sum) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => (l.map fun i => f i g).sum) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact ⟨CkOn_zero, fun m => ⟨0, CCle_zero⟩⟩
  | cons i l ih =>
    have hi := h i (by simp)
    have hl := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨CkOn_add hi.1 hl.1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := hi.2 m
    obtain ⟨c', hc'⟩ := hl.2 m
    exact ⟨c + c', CCle_add hc hc'⟩

end op

theorem operator_in_class_holds : OpCCg := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ d Bg A η F hη hBg hSC hCG hF hFg hz
  set O : Set (B.Mat k r) := {g | Gf k r Bs.z Bs.z' g < η} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ B.GV k r, g ∈ O ∨ g ∈ B.GPos Bs := by
    intro g hg
    by_cases h : Gf k r Bs.z Bs.z' g < η
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hη (not_lt.1 h)⟩
  have hzO : ∀ g ∈ B.GV k r, g ∈ O → F g = 0 := fun g hg h => hz g hg h
  have hoff : ∀ g, g ∉ O → η ≤ Gf k r Bs.z Bs.z' g := fun g h => not_lt.1 h
  have hab1 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coef g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).1⟩
  have hab2 : ∀ T ∈ Θ, ∀ m : ℕ, ∃ C : ℝ, ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ O →
        ‖B.dLR u v T.coefAdj g‖ ≤ C * B.gN g ^ (d + Bg * m) := by
    intro T hT m
    obtain ⟨C, hC⟩ := hCG T hT η hη m
    exact ⟨C, fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (hoff g hgO)).2⟩
  have hApp : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (ap T.coef (B.Rw T.word F)) := by
    intro T hT
    have hR := rwG T.word_lie hF hFg
    have hzR : ∀ g ∈ B.GV k r, g ∈ O → B.Rw T.word F g = 0 := Rw_vanish hO T.word_lie hzO
    have hc := coefLeib hO hcov hBg (hSC T hT).1 (hab1 T hT) hR.1 hR.2 hzR
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨hc.1, fun m => sInCC_mono ?_ le_rfl (hc.2 m)⟩
    nlinarith [mul_le_mul_of_nonneg_left hlen hBg]
  have hAdj : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r)
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m
        (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) := by
    intro T hT
    have hc := coefLeib hO hcov hBg (hSC T hT).2 (hab2 T hT) hF hFg hzO
    have hR := rwG (w := T.word.reverse) (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hc.1 hc.2
    have hlen : (T.word.length : ℝ) ≤ (B.opOrder Θ : ℝ) := by
      exact_mod_cast Formalism.FourierDecayAlt.P.B5.len_le_order Θ hT
    refine ⟨CkOn_smul _ hR.1, fun m => ?_⟩
    have h2 := hR.2 m
    rw [List.length_reverse] at h2
    obtain ⟨c, hcc⟩ := sInCC_mono (A := A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) (by
      nlinarith [mul_le_mul_of_nonneg_left hlen hBg]) le_rfl h2
    exact ⟨_, CCle_smul _ hcc⟩
  exact ⟨listSumG Θ (fun T => ap T.coef (B.Rw T.word F)) hApp,
    listSumG Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) hAdj⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
