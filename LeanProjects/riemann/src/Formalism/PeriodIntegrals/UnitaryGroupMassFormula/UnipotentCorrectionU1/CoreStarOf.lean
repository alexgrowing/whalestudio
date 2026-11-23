import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CCCNonneg

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cDsec

variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Good (k j ρ Q : ℕ) (A₁ : ℝ) (O : Set (B.Mat k (j + ρ))) (F : B.Mat k (j + ρ) → E) (C c : ℝ) : Prop :=
  B.CkOn (Q : ℕ∞) (B.GV k (j + ρ)) F ∧ (∀ g ∈ B.GV k (j + ρ), g ∈ O → F g = 0) ∧
  ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
    ∀ g ∈ B.GV k (j + ρ), B.gN g ^ A₁ * ‖B.dLR u v F g‖ ≤ C * c

theorem cD_add {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {F₁ F₂ : B.Mat k (j + ρ) → E} {C₁ C₂ c : ℝ}
    (h₁ : Good k j ρ Q A₁ O F₁ C₁ c) (h₂ : Good k j ρ Q A₁ O F₂ C₂ c) :
    Good k j ρ Q A₁ O (fun g => F₁ g + F₂ g) (C₁ + C₂) c := by
  obtain ⟨hc1, hz1, hb1⟩ := h₁
  obtain ⟨hc2, hz2, hb2⟩ := h₂
  refine ⟨CkOn_add hc1 hc2, fun g hg hO => by simp only [hz1 g hg hO, hz2 g hg hO, add_zero], ?_⟩
  intro u v hu hv hl g hg
  have hw : ∀ x ∈ wL u ++ wR v, B.inLie k (j + ρ) x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hu X hX).1.1
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hv X hX).1.1
  have hlen : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (Q : ℕ∞) := by
    simp only [wL, wR, List.length_append, List.length_map]
    exact_mod_cast hl
  have hadd := Dw_add hw (sCkOn_mono hlen hc1) (sCkOn_mono hlen hc2) g hg
  have e1 := hb1 u v hu hv hl g hg
  have e2 := hb2 u v hu hv hl g hg
  rw [dLR_eq] at e1 e2 ⊢
  rw [hadd]
  have hpos : 0 ≤ B.gN g ^ A₁ := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  calc B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g + Dw (wL u ++ wR v) F₂ g‖ ≤
        B.gN g ^ A₁ * (‖Dw (wL u ++ wR v) F₁ g‖ + ‖Dw (wL u ++ wR v) F₂ g‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hpos
    _ = B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g‖ + B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₂ g‖ :=
        mul_add _ _ _
    _ ≤ C₁ * c + C₂ * c := add_le_add e1 e2
    _ = (C₁ + C₂) * c := by ring

theorem cD_list {ι : Type*} {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {E₀ : Type*}
    (F : ι → E₀ → B.Mat k (j + ρ) → E) (Pf : E₀ → ℝ → Prop) :
    ∀ l : List ι, (∀ i ∈ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (F i f) C c) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (fun g => (l.map fun i => F i f g).sum) C c := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨0, le_rfl, fun f c _ => ⟨?_, fun g _ _ => by simp, fun u v _ _ _ g _ => ?_⟩⟩
    · simpa using (CkOn_zero (m := (Q : ℕ∞)) (UU := B.GV k (j + ρ)) (E := E))
    · simp only [List.map_nil, List.sum_nil]
      rw [dLR_eq, Dw_zero]
      simp
  | cons a l ih =>
    intro h
    obtain ⟨C₁, hC₁, h₁⟩ := h a (List.mem_cons_self ..)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun f c hf => ?_⟩
    have := cD_add (h₁ f c hf) (h₂ f c hf)
    simpa only [List.map_cons, List.sum_cons] using this

theorem cD_delta {χ : ℂ → ℂ} (hχ : IsCutC χ) : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport χ, δ ≤ ‖z‖ := by
  obtain ⟨-, -, h0⟩ := hχ
  have ho : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨ε, hε, fun z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hz

end cDsec

section cDterm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cD_term (hP : PolyB) (hC : DjCurve) {k j ρ κ d Q o mm₀ : ℕ} {A₀ : ℝ}
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {χ : ℂ → ℂ} (hχ : IsCutC χ) {δ : ℝ} (hδ : 0 < δ)
    (hδχ : ∀ z ∈ tsupport χ, δ ≤ ‖z‖) {φ : B.Mat k (j + ρ) → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ0 : ∀ g, DjU k j ρ g ∉ tsupport χ → φ g = 0) {Cφ : ℝ}
    (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) (hQ : Q + o ≤ mm₀)
    (T : B.DTerm k (j + ρ) Wp Wq)
    (hT : T.word.length ≤ o ∧ ∃ (P : B.Mat k (j + ρ) → ℂ) (a b : ℕ), IsPolyDeg κ P ∧
      ∀ g, T.coef g = (P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) •
        ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Good k j ρ Q (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ))
        {g | DjU k j ρ g ∉ tsupport χ} (ap T.coef (B.Rw T.word (fun g => φ g • f g))) C c := by
  obtain ⟨hwo, P, a, b, hPd, hcoef⟩ := hT
  have hPs := (hP k (j + ρ) κ P hPd).1
  set s : B.Mat k (j + ρ) → ℂ := fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b with hs
  set Lid : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
  have hLn : ∀ z : ℂ, ‖Lid z‖ ≤ ‖z‖ := by
    intro z
    simp only [Lid, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le))
  have hce : T.coef = fun g => Lid (s g) := by
    funext g; rw [hcoef g]; simp [Lid, s]
  set O : Set (B.Mat k (j + ρ)) := {g | DjU k j ρ g ∉ tsupport χ}
  have hO : IsOpen O := (isClosed_tsupport χ).isOpen_compl.preimage hD.continuous
  set UU : Set (B.Mat k (j + ρ)) := {g | DjU k j ρ g ≠ 0}
  have hUU : IsOpen UU := isOpen_ne_fun hD.continuous continuous_const
  have hcov : ∀ g ∈ B.GV k (j + ρ), g ∈ O ∨ g ∈ UU := by
    intro g _
    by_cases h : DjU k j ρ g ∈ tsupport χ
    · right; intro h0; exact hχ.2.2 (h0 ▸ h)
    · left; exact h
  have hsUU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s UU := cB_smooth hD hPs a b
  have hsCk : ∀ m : ℕ∞, B.CkOn m UU s := fun m g₀ hg₀ =>
    ⟨UU, s, hUU, hg₀, hsUU.of_le (by exact_mod_cast le_top), fun _ _ _ => rfl⟩
  have hcoefCk : ∀ m : ℕ∞, B.CkOn m UU T.coef := fun m g₀ hg₀ =>
    ⟨UU, T.coef, hUU, hg₀, by
      rw [hce]; exact ((Lid.restrictScalars ℝ).contDiff.comp_contDiffOn hsUU).of_le (by exact_mod_cast le_top),
      fun _ _ _ => rfl⟩
  obtain ⟨CB, hCB0, hCB⟩ := cB_bound hP hC hPd a b Q hδ
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := cC_bound (E := Wq →L[ℂ] Wp) (A₀ := A₀) hφ hWB T.word_lie hwo hQ
  refine ⟨2 ^ Q * CB * CΨ, by positivity, fun f c hf => ?_⟩
  have hc0 := cC_c_nonneg hf
  set Ψ := B.Rw T.word (fun g => φ g • f g) with hΨ
  have hΨck : B.CkOn (Q : ℕ∞) (B.GV k (j + ρ)) Ψ := cC_Psi_ck hφ hf.1 T.word_lie (by omega)
  have hΨz : ∀ g ∈ B.GV k (j + ρ), g ∈ O → Ψ g = 0 :=
    Rw_vanish hO T.word_lie (fun g _ hgO => by simp [hφ0 g hgO])
  have hPr : Pr O UU (Q : ℕ∞) T.coef Ψ := ⟨hcoefCk Q, hΨck, hΨz⟩
  refine ⟨hPr.ck hO hcov, fun g hg hgO => (hPr.mono zero_le).apz g hg hgO, ?_⟩
  intro u v hu hv hl g hg
  have hlie := lie_LR (fun X hX => (hu X hX).1.1) (fun X hX => (hv X hX).1.1)
  have hp := gN_pos hg
  rw [dLR_eq]
  by_cases hgO : g ∈ O
  · rw [Dw_vanish hO hlie (hPr.mono zero_le).apz g hg hgO]
    simp only [norm_zero, mul_zero]
    positivity
  · have hDg : DjU k j ρ g ∈ tsupport χ := not_not.mp hgO
    have hgU : g ∈ UU := fun h0 => hχ.2.2 (h0 ▸ hDg)
    have hδg := hδχ _ hDg
    set Eφ : ℝ := (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) with hEφ
    set M : ℝ := CB * B.gN g ^ (κ : ℝ) * (CΨ * c * B.gN g ^ (Eφ - A₀)) with hM
    have hM0 : 0 ≤ M := by positivity
    have hb := leib_bound hO hcov g hg M (wL u ++ wR v) T.coef Ψ hlie
      (hPr.mono (by rw [len_LR]; exact_mod_cast hl)) (by
        intro w₁ w₂ h₁ h₂ _
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR h₁
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR h₂
        have hu₁P : unitP k j ρ u₁ := fun X hX => hu X (hu₁.subset hX)
        have hv₁P : unitP k j ρ v₁ := fun X hX => hv X (hv₁.subset hX)
        have hu₂P : unitP k j ρ u₂ := fun X hX => hu X (hu₂.subset hX)
        have hv₂P : unitP k j ρ v₂ := fun X hX => hv X (hv₂.subset hX)
        have hlie₁ := lie_LR (fun X hX => (hu₁P X hX).1.1) (fun X hX => (hv₁P X hX).1.1)
        have hl₁ : u₁.length + v₁.length ≤ Q := by
          have := hu₁.length_le; have := hv₁.length_le; omega
        have hl₂ : u₂.length + v₂.length ≤ Q := by
          have := hu₂.length_le; have := hv₂.length_le; omega
        rw [hce, cA_Dw_clm Lid hUU _ hlie₁ (hsCk _) g hg hgU, ← dLR_eq]
        have b1 : ‖Lid (B.dLR u₁ v₁ s g)‖ ≤ CB * B.gN g ^ (κ : ℝ) :=
          (hLn _).trans (by rw [dLR_eq]; exact hCB u₁ v₁ hu₁P hv₁P hl₁ g hg hδg)
        have b2 : ‖Dw (wL u₂ ++ wR v₂) Ψ g‖ ≤ CΨ * c * B.gN g ^ (Eφ - A₀) := by
          rw [← dLR_eq]; exact hCΨ f c hf u₂ v₂ hu₂P hv₂P hl₂ g hg
        exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
    have hexp : B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
        B.gN g ^ (κ : ℝ) * B.gN g ^ (Eφ - A₀) = 1 := by
      rw [← Real.rpow_add hp, ← Real.rpow_add hp]
      rw [show A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ) + (κ : ℝ) + (Eφ - A₀) = 0 by
        rw [hEφ]; ring]
      exact Real.rpow_zero _
    have hpow : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ Q := by
      rw [len_LR]; exact pow_le_pow_right₀ (by norm_num) hl
    calc B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
          ‖Dw (wL u ++ wR v) (ap T.coef Ψ) g‖
        ≤ B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) * (2 ^ Q * M) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right hpow hM0))
            (Real.rpow_nonneg hp.le _)
      _ = 2 ^ Q * CB * CΨ * c * (B.gN g ^ (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) *
          B.gN g ^ (κ : ℝ) * B.gN g ^ (Eφ - A₀)) := by rw [hM]; ring
      _ = 2 ^ Q * CB * CΨ * c := by rw [hexp, mul_one]

end cDterm

theorem coreStar_of (hP : PolyB) (hDp : DjPoly) (hC : DjCurve) : CoreStar := by
  intro k j ρ Wp Wq _ _ _ _ _ o κ d Θ χ φ hΘ hχ Q mm₀ A₀ hQ hφ hφ0 hWBe
  obtain ⟨Cφ, hWB⟩ := hWBe
  have hD := (hP k (j + ρ) j (DjU k j ρ) (hDp k j ρ)).1
  obtain ⟨δ, hδ, hδχ⟩ := cD_delta hχ
  obtain ⟨C, _, hCg⟩ := cD_list (k := k) (j := j) (ρ := ρ) (Q := Q)
    (A₁ := A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) (O := {g | DjU k j ρ g ∉ tsupport χ})
    (fun (T : B.DTerm k (j + ρ) Wp Wq) (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) =>
      ap T.coef (B.Rw T.word (fun g => φ g • f g)))
    (fun f c => B.CCle A₀ mm₀ f c) Θ
    (fun T hT => cD_term hP hC hD hχ hδ hδχ hφ hφ0 hWB hQ T (hΘ T hT))
  refine ⟨C, fun f c hf => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hCg f c hf
  refine ⟨h1, fun g hg hne => ?_, h3⟩
  by_contra hK
  exact hne (h2 g hg (fun hD' => hK ⟨_, hD', rfl⟩))

end PI.UnitaryCorollaryDerivatives
