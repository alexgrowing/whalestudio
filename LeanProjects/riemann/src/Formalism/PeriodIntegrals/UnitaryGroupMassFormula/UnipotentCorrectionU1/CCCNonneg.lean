import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CBLamnorm

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cCsec

variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cC_c_nonneg {r : ℕ} {A : ℝ} {m : ℕ} {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)
  have h := hf.2 [] [] (by simp) (by simp) (by simp) 1 h1
  have hpos := gN_pos h1
  exact le_trans (mul_nonneg (Real.rpow_nonneg hpos.le _) (norm_nonneg _)) h

theorem cC_smul_ck {r : ℕ} {m : ℕ∞} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k r) (fun g => φ g • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => φ g • f' g, hU, hgU, ?_, fun g hg hgv => by simp only [hff g hg hgv]⟩
  exact ((hφ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn).smul hf'

theorem cC_Psi_ck {r : ℕ} {Q mm : ℕ} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn (mm : ℕ∞) (B.GV k r) f) {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    (hQ : Q + w.length ≤ mm) : B.CkOn (Q : ℕ∞) (B.GV k r) (B.Rw w (fun g => φ g • f g)) := by
  have h := cC_smul_ck hφ hf
  have hmono : B.CkOn ((Q + w.length : ℕ) : ℕ∞) (B.GV k r) (fun g => φ g • f g) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hQ), hff⟩
  have hR : B.Rw w (fun g => φ g • f g) = Dw (wL [] ++ wR w) (fun g => φ g • f g) := by
    rw [← dLR_eq]
    rfl
  rw [hR]
  apply CkOn_Dw
  · intro x hx
    simp only [wL, wR, List.map_nil, List.nil_append, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · simpa [wL, wR] using hmono

theorem cC_cost {Q o d : ℕ} {u v u₁ v₁ w : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v)
    (hl : u.length + v.length ≤ Q) (hwo : w.length ≤ o) (hu₁ : u₁.Sublist u) (hv₁ : v₁.Sublist (v ++ w.map nrm)) :
    ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ) ≤ (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) := by
  have hu0 : ∀ X ∈ u, costP k j ρ X = 0 := fun X hX => by simp [costP, (hu X hX).1]
  have hv0 : ∀ X ∈ v, costP k j ρ X = 0 := fun X hX => by simp [costP, (hv X hX).1]
  have hle : ∀ X, costP k j ρ X ≤ j := fun X => by
    unfold costP
    split_ifs <;> omega
  have hA : ((u₁ ++ v₁).map (costP k j ρ)).sum ≤ j * o := by
    rw [List.map_append, List.sum_append]
    have h1 : (u₁.map (costP k j ρ)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
      exact hu0 X (hu₁.subset hX)
    have h2 : (v₁.map (costP k j ρ)).sum ≤ ((v ++ w.map nrm).map (costP k j ρ)).sum :=
      (hv₁.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
    have h3 : ((v ++ w.map nrm).map (costP k j ρ)).sum ≤ j * w.length := by
      rw [List.map_append, List.sum_append]
      have h0 : (v.map (costP k j ρ)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
        exact hv0 X hX
      rw [h0, zero_add, List.map_map]
      calc ((w.map (costP k j ρ ∘ nrm))).sum ≤ (w.map (fun _ => j)).sum :=
            List.sum_le_sum (fun X _ => hle _)
        _ = j * w.length := by simp [mul_comm]
    have h4 : j * w.length ≤ j * o := Nat.mul_le_mul_left _ hwo
    omega
  have hL : (u₁ ++ v₁).length ≤ Q + o := by
    have := hu₁.length_le
    have := hv₁.length_le
    simp only [List.length_append, List.length_map] at *
    omega
  have key : ((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum ≤ j * o + d * (Q + o) := by
    rw [List.sum_map_add]
    have hd : ((u₁ ++ v₁).map (fun _ => d)).sum = (u₁ ++ v₁).length * d := by simp
    rw [hd]
    have : (u₁ ++ v₁).length * d ≤ d * (Q + o) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hL
    omega
  exact_mod_cast key

theorem cC_bound {d Q o mm₀ : ℕ} {A₀ : ℝ} {φ : B.Mat k (j + ρ) → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {Cφ : ℝ}
    (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) {w : List (B.Mat k (j + ρ))}
    (hw : ∀ X ∈ w, B.inLie k (j + ρ) X) (hwo : w.length ≤ o) (hQ : Q + o ≤ mm₀) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ (f : B.Mat k (j + ρ) → E) (c : ℝ), B.CCle A₀ mm₀ f c →
      ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
        ∀ g ∈ B.GV k (j + ρ), ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖ ≤
          CΨ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
  classical
  have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := j + ρ)
  have hCφ : 0 ≤ Cφ := by
    have h := hWB [] [] (by simp) (by simp) (by simp) 1 h1
    have hX := Real.rpow_pos_of_pos (gN_pos h1)
      ((0 : ℝ) + ((([] ++ [] : List (B.Mat k (j + ρ))).map (fun X => costP k j ρ X + d)).sum : ℕ))
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hX
    linarith [norm_nonneg (B.dLR [] [] φ 1)]
  have hw'lie : ∀ X ∈ w.map nrm, B.unitLie k (j + ρ) X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact nrm_unit (hw Y hY)
  obtain ⟨a, ha⟩ : ∃ a : B.Mat k (j + ρ) → (E →L[ℂ] E),
      a = fun g => φ g • ContinuousLinearMap.id ℂ E := ⟨_, rfl⟩
  have ha_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
    rw [ha]
    exact hφ.smul contDiff_const
  have hφU : ∀ n : ℕ∞, B.CkOn n Set.univ φ := fun n g₀ _ =>
    ⟨Set.univ, φ, isOpen_univ, trivial, hφ.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top),
      fun _ _ _ => rfl⟩
  refine ⟨|((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ, mul_nonneg (by positivity) hCφ,
    fun f c hf u v hu hv hl g hg => ?_⟩
  have hc : 0 ≤ c := cC_c_nonneg hf
  have hgN := gN_ge_one hg
  have hgN0 := gN_pos hg
  have hG : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) (B.GV k (j + ρ))
      (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    cC_Psi_ck hφ hf.1 (fun X hX => (hw'lie X hX).1) (by simp only [List.length_map]; omega)
  obtain ⟨V, G', hVo, hgV, hG'c, hG'eq⟩ := hG g hg
  have hGV : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) V (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
    fun g₀ hg₀ => ⟨V, G', hVo, hg₀, hG'c, hG'eq⟩
  have hscale := cA_Dw_clm (E' := E) ((((w.map nz).prod : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) hVo
    (wL u ++ wR v) (fun x hx => ((cB_wP hu hv) x hx).1.1) (by simpa [wL, wR] using hGV) g hg hgV
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hscale
  have hsplit : Dw (wL u ++ wR (v ++ w.map nrm)) (fun g => φ g • f g) =
      Dw (wL u ++ wR v) (B.Rw (w.map nrm) (fun g => φ g • f g)) := by
    rw [show wR (v ++ w.map nrm) = wR v ++ wR (w.map nrm) from List.map_append,
      ← List.append_assoc, Dw_append, Dw_wR]
  have hF : (fun g => φ g • f g) = ap a f := by
    funext g
    simp [ap, ha]
  have hW'lie : ∀ x ∈ wL u ++ wR (v ++ w.map nrm), B.inLie k (j + ρ) x.2 := by
    intro x hx
    simp only [wL, wR, List.map_append, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1.1
    · exact (hv X hX).1.1
    · exact (hw'lie X (List.mem_map.2 hX)).1
  have hlen : (wL u ++ wR (v ++ w.map nrm)).length = u.length + v.length + w.length := by
    simp [wL, wR]
    omega
  have hPr : Pr ∅ Set.univ ((wL u ++ wR (v ++ w.map nrm)).length : ℕ∞) a f := by
    refine ⟨fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial,
      ha_smooth.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top), fun _ _ _ => rfl⟩, fun g₀ hg₀ => ?_,
      fun g _ hg => absurd hg (Set.notMem_empty g)⟩
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf.1 g₀ hg₀
    refine ⟨U, f', hU, hgU, hf'.of_le ?_, hff⟩
    rw [hlen]
    exact_mod_cast (by omega : u.length + v.length + w.length ≤ mm₀)
  have hbound : ∀ w₁ w₂ : List (Bool × B.Mat k (j + ρ)), w₁.Sublist (wL u ++ wR (v ++ w.map nrm)) →
      w₂.Sublist (wL u ++ wR (v ++ w.map nrm)) → w₁.length + w₂.length = (wL u ++ wR (v ++ w.map nrm)).length →
      ‖Dw w₁ a g‖ * ‖Dw w₂ f g‖ ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
    intro w₁ w₂ hw₁ hw₂ _
    obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hw₁
    obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hw₂
    have hunit : ∀ X ∈ v ++ w.map nrm, B.unitLie k (j + ρ) X := by
      intro X hX
      rcases List.mem_append.1 hX with hX | hX
      · exact cB_unitLie hv X hX
      · exact hw'lie X hX
    have hA : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) := by
      have hDa := cA_Dw_clm (E := ℂ) (E' := E →L[ℂ] E)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ E))
        isOpen_univ (wL u₁ ++ wR v₁) (fun x hx => hW'lie x (hw₁.subset hx)) (hφU _) g hg trivial
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hDa
      rw [ha, hDa, norm_smul, ← dLR_eq]
      have hWB1 := hWB u₁ v₁ (fun X hX => cB_unitLie hu X (hu₁.subset hX))
        (fun X hX => hunit X (hv₁.subset hX))
        (by have := hu₁.length_le; have := hv₁.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      have hcost := cC_cost hu hv hl hwo hu₁ hv₁ (d := d)
      have hexp : B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) ≤
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hgN (by linarith)
      calc ‖B.dLR u₁ v₁ φ g‖ * ‖ContinuousLinearMap.id ℂ E‖ ≤ ‖B.dLR u₁ v₁ φ g‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
        _ ≤ Cφ * B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) := by
            rw [mul_one]; exact hWB1
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp hCφ
    have hB : ‖Dw (wL u₂ ++ wR v₂) f g‖ ≤ c * B.gN g ^ (-A₀) := by
      rw [← dLR_eq]
      have h2 := hf.2 u₂ v₂ (fun X hX => cB_unitLie hu X (hu₂.subset hX))
        (fun X hX => hunit X (hv₂.subset hX))
        (by have := hu₂.length_le; have := hv₂.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
      rw [Real.rpow_neg hgN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgN0 _), mul_comm]
      exact h2
    calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) f g‖
        ≤ (Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ))) * (c * B.gN g ^ (-A₀)) :=
          mul_le_mul hA hB (norm_nonneg _) (mul_nonneg hCφ (Real.rpow_nonneg hgN0.le _))
      _ = Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
          rw [sub_eq_add_neg, Real.rpow_add hgN0 ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) (-A₀)]
          ring
  have hleib := leib_bound isOpen_empty (fun g _ => Or.inr trivial) g hg
    (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀)) (wL u ++ wR (v ++ w.map nrm)) a f
    hW'lie hPr hbound
  have hM : 0 ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) :=
    mul_nonneg (mul_nonneg hCφ hc) (Real.rpow_nonneg hgN0.le _)
  have hpow : (2 : ℝ) ^ (wL u ++ wR (v ++ w.map nrm)).length ≤ 2 ^ (Q + o) :=
    pow_le_pow_right₀ (by norm_num) (by rw [hlen]; omega)
  calc ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖
      = |((w.map nz).prod : ℝ)| * ‖Dw (wL u ++ wR (v ++ w.map nrm)) (ap a f) g‖ := by
        rw [Rw_scale, dLR_eq, hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← hF, hsplit]
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (wL u ++ wR (v ++ w.map nrm)).length *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left hleib (abs_nonneg _)
    _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (Q + o) *
          (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) (abs_nonneg _)
    _ = |((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ * c *
          B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by ring

end cCsec

end PI.UnitaryCorollaryDerivatives
