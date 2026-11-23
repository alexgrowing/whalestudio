import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompCA

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LatticeLocalGlobalTheory

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA

variable {k r : ℕ}

def Good (k r n : ℕ) (w : List (Bool × B.Mat k r)) : Prop :=
  ∃ u v : List (B.Mat k r), (∀ X ∈ u, unitLie k r X) ∧ (∀ X ∈ v, unitLie k r X) ∧
    u.length + v.length ≤ n ∧ w = wL u ++ wR v

lemma Good.sub {n : ℕ} {w w' : List (Bool × B.Mat k r)} (h : Good k r n w) (hs : w'.Sublist w) :
    Good k r n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := h
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hs
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega

def cw (cost : B.Mat k r → ℕ) (w : List (Bool × B.Mat k r)) : ℕ := (w.map (fun x => cost x.2)).sum

lemma cw_perm (cost : B.Mat k r → ℕ) {w₁ w₂ w : List (Bool × B.Mat k r)} (hp : (w₁ ++ w₂).Perm w) :
    cw cost w₁ + cw cost w₂ = cw cost w := by
  unfold cw
  rw [← List.sum_append, ← List.map_append]
  exact (hp.map _).sum_eq

lemma cw_snoc (cost : B.Mat k r → ℕ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r) :
    cw cost (w ++ [x]) = cw cost w + cost x.2 := by
  simp [cw, List.map_append, List.sum_append]

lemma cw_LR (cost : B.Mat k r → ℕ) (u v : List (B.Mat k r)) :
    cw cost (wL u ++ wR v) = ((u ++ v).map cost).sum := by
  simp [cw, wL, wR, List.map_append, List.map_map, Function.comp_def]

lemma gN_nn (g : B.Mat k r) : 0 ≤ gN g := by
  first
  | (unfold gN; positivity)
  | (simp only [gN]; positivity)
  | (unfold B.gN; positivity)

theorem faa (n : ℕ) (cost : B.Mat k r → ℕ) (ψ : B.Mat k r → ℂ) (hψ : ContDiff ℝ ∞ ψ) (K : Set ℂ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (H : ∀ w, Good k r n w → w ≠ [] → ∀ g ∈ GV k r, ψ g ∈ K → ‖Dw w ψ g‖ ≤ C₀ * gN g ^ cw cost w) :
    ∀ m : ℕ, ∀ χ : ℂ → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ w, Good k r n w → w.length ≤ m → ∀ g ∈ GV k r, ψ g ∈ K →
        ‖Dw w (fun g => χ (ψ g)) g‖ ≤ C * gN g ^ cw cost w := by
  intro m
  induction m with
  | zero =>
    intro χ hχ hχc
    obtain ⟨c, hc⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    refine ⟨max c 0, le_max_right _ _, fun w _ hw g _ _ => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    simp only [Dw, List.foldr_nil, cw, List.map_nil, List.sum_nil, pow_zero, mul_one]
    exact (hc _).trans (le_max_left _ _)
  | succ m ih =>
    intro χ hχ hχc
    obtain ⟨K₀, hK₀, h₀⟩ := ih χ hχ hχc
    obtain ⟨K₁, hK₁, h₁⟩ := ih _ (sm_fd hχ 1) (hχc.fderiv_apply (𝕜 := ℝ) 1)
    obtain ⟨K₂, hK₂, h₂⟩ := ih _ (sm_fd hχ Complex.I) (hχc.fderiv_apply (𝕜 := ℝ) Complex.I)
    refine ⟨max K₀ (2 ^ m * ((K₁ + K₂) * C₀)), le_max_of_le_left hK₀, fun w hw hlen g hg hgK => ?_⟩
    have hgN := gN_nn g
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact (h₀ w hw (by omega) g hg hgK).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hgN _))
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length = m := by simp at hlen hge; omega
      rw [Dw_snoc, Dx_comp x hχ hψ]
      have hA : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) 1) := (sm_fd hχ 1).comp hψ
      have hB : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) Complex.I) := (sm_fd hχ Complex.I).comp hψ
      have hR : ContDiff ℝ ∞ (fun g => reC (Dx x ψ g)) := reC.contDiff.comp (sm_Dx x hψ)
      have hI : ContDiff ℝ ∞ (fun g => imC (Dx x ψ g)) := imC.contDiff.comp (sm_Dx x hψ)
      rw [Dw_add' w' (hA.mul hR) (hB.mul hI)]
      have key : ∀ (L : ℂ →L[ℝ] ℂ), (∀ z, ‖L z‖ ≤ ‖z‖) → ∀ (v : ℂ) (Kv : ℝ), 0 ≤ Kv →
          (∀ w₁, Good k r n w₁ → w₁.length ≤ m →
            ‖Dw w₁ (fun g => fderiv ℝ χ (ψ g) v) g‖ ≤ Kv * gN g ^ cw cost w₁) →
          ‖Dw w' (fun g => fderiv ℝ χ (ψ g) v * L (Dx x ψ g)) g‖ ≤
            2 ^ m * (Kv * C₀) * gN g ^ cw cost (w' ++ [x]) := by
        intro L hL v Kv hKv hv
        have hM := leibC g w' (fun g => fderiv ℝ χ (ψ g) v) (fun g => L (Dx x ψ g))
          ((sm_fd hχ v).comp hψ) (L.contDiff.comp (sm_Dx x hψ)) (Kv * C₀ * gN g ^ cw cost (w' ++ [x])) (by
            intro w₁ w₂ s1 s2 hp
            have hG1 : Good k r n w₁ := hw.sub (s1.trans (List.sublist_append_left _ _))
            have hG2 : Good k r n (w₂ ++ [x]) := hw.sub (s2.append (List.Sublist.refl _))
            have hl1 : w₁.length ≤ m := by have := s1.length_le; omega
            have e1 := hv w₁ hG1 hl1
            have e2 := H (w₂ ++ [x]) hG2 (by simp) g hg hgK
            rw [Dw_snoc] at e2
            rw [Dw_clm w₂ L (sm_Dx x hψ)]
            have hcs : cw cost w₁ + cw cost (w₂ ++ [x]) = cw cost (w' ++ [x]) :=
              cw_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])
            calc _ ≤ (Kv * gN g ^ cw cost w₁) * (C₀ * gN g ^ cw cost (w₂ ++ [x])) :=
                  mul_le_mul e1 ((hL _).trans e2) (norm_nonneg _) (mul_nonneg hKv (pow_nonneg hgN _))
              _ = Kv * C₀ * gN g ^ cw cost (w' ++ [x]) := by rw [← hcs, pow_add]; ring)
        calc _ ≤ 2 ^ w'.length * (Kv * C₀ * gN g ^ cw cost (w' ++ [x])) := hM
          _ = _ := by rw [hlen']; ring
      have t1 := key reC norm_reC 1 K₁ hK₁ (fun w₁ hG hl => h₁ w₁ hG hl g hg hgK)
      have t2 := key imC norm_imC Complex.I K₂ hK₂ (fun w₁ hG hl => h₂ w₁ hG hl g hg hgK)
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 ^ m * (K₁ * C₀) * gN g ^ cw cost (w' ++ [x]) +
            2 ^ m * (K₂ * C₀) * gN g ^ cw cost (w' ++ [x]) := add_le_add t1 t2
        _ = (2 ^ m * ((K₁ + K₂) * C₀)) * gN g ^ cw cost (w' ++ [x]) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hgN _)

end LatticeLocalGlobalTheory

private theorem Dw_comp_eq_zero_of_not_mem_tsupport {k r : ℕ} (ψ : B.Mat k r → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    ∀ m : ℕ, ∀ χ : ℂ → ℂ, ContDiff ℝ ∞ χ → ∀ w : List (Bool × B.Mat k r), w.length ≤ m →
      ∀ g, ψ g ∉ tsupport χ → P.BetaSesquilinearity.Dw w (fun g => χ (ψ g)) g = 0 := by
  intro m
  induction m with
  | zero =>
    intro χ hχ w hw g hg
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    show χ (ψ g) = 0
    first
    | exact image_eq_zero_of_notMem_tsupport hg
    | exact image_eq_zero_of_nmem_tsupport hg
  | succ m ih =>
    intro χ hχ w hw g hg
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact ih χ hχ w (by omega) g hg
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length ≤ m := by simp at hw; omega
      rw [CCA.Dw_snoc, CCA.Dx_comp x hχ hψ]
      have hA : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) 1) := (CCA.sm_fd hχ 1).comp hψ
      have hB : ContDiff ℝ ∞ (fun g => fderiv ℝ χ (ψ g) Complex.I) := (CCA.sm_fd hχ Complex.I).comp hψ
      have hR : ContDiff ℝ ∞ (fun g => CCA.reC (P.BetaSesquilinearity.Dx x ψ g)) := CCA.reC.contDiff.comp (CCA.sm_Dx x hψ)
      have hI : ContDiff ℝ ∞ (fun g => CCA.imC (P.BetaSesquilinearity.Dx x ψ g)) := CCA.imC.contDiff.comp (CCA.sm_Dx x hψ)
      rw [CCA.Dw_add' w' (hA.mul hR) (hB.mul hI)]
      have key : ∀ (L : ℂ →L[ℝ] ℂ) (v : ℂ),
          P.BetaSesquilinearity.Dw w' (fun g => fderiv ℝ χ (ψ g) v * L (P.BetaSesquilinearity.Dx x ψ g)) g = 0 := by
        intro L v
        have hM := CCA.leibC g w' (fun g => fderiv ℝ χ (ψ g) v) (fun g => L (P.BetaSesquilinearity.Dx x ψ g))
          ((CCA.sm_fd hχ v).comp hψ) (L.contDiff.comp (CCA.sm_Dx x hψ)) 0 (by
            intro w₁ w₂ s1 _ _
            have hg' : ψ g ∉ tsupport (fun z => fderiv ℝ χ z v) :=
              fun h => hg (tsupport_fderiv_apply_subset (𝕜 := ℝ) v h)
            rw [ih _ (CCA.sm_fd hχ v) w₁ (by have := s1.length_le; omega) g hg']
            simp)
        simpa using hM
      beta_reduce
      rw [key CCA.reC 1, key CCA.imC Complex.I, add_zero]

theorem compact_curve_estimate : CompC := by
  intro k r ψ χ cost n C₀ hψ hχ hχc H
  obtain ⟨C, hC0, hC⟩ := LatticeLocalGlobalTheory.faa n cost ψ hψ (tsupport χ) (max C₀ 0) (le_max_right _ _) (by
      rintro w ⟨u, v, hu, hv, hl, rfl⟩ hne g hg hgK
      have hne' : u ++ v ≠ [] := by
        rintro h0
        rw [List.append_eq_nil_iff] at h0
        obtain ⟨rfl, rfl⟩ := h0
        exact hne (by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR])
      have key := H u v hu hv hl hne' g hg hgK
      rw [P.BetaSesquilinearity.dLR_eq, Real.rpow_natCast, ← LatticeLocalGlobalTheory.cw_LR] at key
      exact key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (LatticeLocalGlobalTheory.gN_nn g) _)))
    n χ hχ hχc
  refine ⟨C, fun u v hu hv hl g hg => ?_⟩
  rw [P.BetaSesquilinearity.dLR_eq, zero_add, Real.rpow_natCast, ← LatticeLocalGlobalTheory.cw_LR]
  have hlen : (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).length ≤ n := by simpa [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR] using hl
  by_cases hgK : ψ g ∈ tsupport χ
  · exact hC _ ⟨u, v, hu, hv, hl, rfl⟩ hlen g hg hgK
  · rw [Dw_comp_eq_zero_of_not_mem_tsupport ψ hψ n χ hχ _ hlen g hgK, norm_zero]
    exact mul_nonneg hC0 (pow_nonneg (LatticeLocalGlobalTheory.gN_nn g) _)

end PI.UnitaryCorollaryDerivatives
