import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.DensLemmaOfCut

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

structure TopModel where
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℂ V]
  [cs : CompleteSpace V]

attribute [instance] TopModel.ng TopModel.ns TopModel.cs

def TopDensity (C₂ C CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    ∃ (β : ℂ) (p m' : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (M : TopModel)
      (Φ0 : G.Mat (p + (m' + 1 + 1)) → M.V) (e : ℕ → ℝ) (K Cp : ℝ) (P : Seminorm ℂ M.V) (D' z₀ : ℂ),
      β ≠ 0 ∧ (∀ a, d a ≠ 0) ∧ p + (m' + 1 + 1) = r + 1 ∧ D' ≠ 0 ∧
      z₀ ∈ G.rootSet (m' + 2) ((-1) ^ (m' + 3) * D') ∧ 0 ≤ Cp ∧ (∀ v, P v ≤ Cp * ‖v‖) ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = D' →
        P (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c) = 0) ∧
      (P (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z₀) = 0 → orbI D γ θ F' = 0)

theorem mainTerm_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : G.Mat (m + 1 + 1) → V) (D' x : ℂ) :
    G.mainTerm β m (fun _ => 1) Φ x⁻¹ D' =
      ∑ j : Fin (G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).card,
        G.psi β ((((m : ℂ) + 2) * ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) * x) •
          ((((m : ℂ) + 2)⁻¹ * ((‖((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)‖ ^
              ((m + 1) ^ 2) : ℝ) : ℂ)) •
            G.OmLong β (m + 1) Φ ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) := by
  set S := G.rootSet (m + 2) ((-1) ^ (m + 3) * D')
  unfold G.mainTerm
  rw [Finset.smul_sum, ← Finset.sum_coe_sort S,
    ← Equiv.sum_comp S.equivFin.symm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, smul_smul, div_inv_eq_mul]
  congr 1
  ring

theorem av_shift (CV r n : ℕ) (hn : 3 ≤ n) : AV (CV / 2) r (n + 1) ≤ AV CV r n := by
  unfold AV
  have h2 : ((CV / 2 : ℕ) : ℝ) * 2 ≤ (CV : ℝ) := by
    have : CV / 2 * 2 ≤ CV := Nat.div_mul_le_self CV 2
    exact_mod_cast this
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (0 : ℝ) ≤ ((CV / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hX : (r : ℝ) ^ 3 * ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 4 ≤
      2 * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := by
    push_cast
    have hr3 : (0 : ℝ) ≤ (r : ℝ) ^ 3 := by positivity
    have hr4 : (0 : ℝ) ≤ (r : ℝ) ^ 4 := by positivity
    nlinarith
  have hY : (0 : ℝ) ≤ (r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4 := by positivity
  calc ((CV / 2 : ℕ) : ℝ) * ((r : ℝ) ^ 3 * ((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 4)
      ≤ ((CV / 2 : ℕ) : ℝ) * (2 * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left hX hc
    _ = (((CV / 2 : ℕ) : ℝ) * 2) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := by ring
    _ ≤ (CV : ℝ) * ((r : ℝ) ^ 3 * n + (n : ℝ) ^ 2 + (r : ℝ) ^ 4) := mul_le_mul_of_nonneg_right h2 hY

theorem downTop_of_parts (hU : U.UseGermTop) (hAv : AveragingZero) (hT : DensThreshTop)
    (hD : ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV → TopDensity C₂ C CV) :
    ∃ C₀ : ℕ, ∀ CV, C₀ ≤ CV → DownTop CV := by
  obtain ⟨C₁, C₂, hU⟩ := hU
  obtain ⟨C, CV₀, hD⟩ := hD C₂
  obtain ⟨CV₁, hT⟩ := hT ((C₁ : ℝ) + 1) (C : ℝ) C₂ (by positivity) (by positivity)
  refine ⟨max CV₀ (2 * CV₁), fun CV hCV => ?_⟩
  intro hSA m hZ k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ μR θ i hH hy hrel hG hz hrun hθ hi
  obtain ⟨β, p, m', σ, d, M, Φ0, e, K, Cp, P, D', z₀, hβ, hd, hps, hD', hz₀, hCp, hP, hdec, he, ⟨δ, hδ, hlow⟩, hslice⟩ :=
    hD CV (le_of_max_le_left hCV) hSA m hZ k r Wp Wq D A ε mm F' γ μR θ i hH hy hrel hG hz hrun hθ hi
  have hr : 1 ≤ r := hy.1
  have hA : (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A := hy.2.2.1
  have hA' : (r : ℝ) * AV (CV / 2) r (2 * r + k + 2) ≤ A :=
    le_trans (mul_le_mul_of_nonneg_left (av_shift CV r (2 * r + k + 1) (by omega)) (Nat.cast_nonneg _)) hA
  have hCV1 : CV₁ ≤ CV / 2 := by have := le_of_max_le_right hCV; omega
  have hcast : ((p + (m' + 1 + 1) : ℕ) : ℝ) = (r : ℝ) + 1 := by rw [hps]; push_cast; ring
  have hexp : ∀ j ≤ C₂ * (m' + 2) ^ 2,
      ((C₁ : ℝ) + 1) * ((m' : ℝ) + 2) ^ 2 ≤ e j / (5 * ((p + (m' + 1 + 1) : ℕ) : ℝ)) ∧
      2 * ((p + (m' + 1 + 1) : ℕ) : ℝ) ^ 2 < e j / (5 * ((p + (m' + 1 + 1) : ℕ) : ℝ)) := by
    intro j hj
    have h1 := (hT (CV / 2) hCV1 r (2 * r + k + 2) (m' + 2) j A hr (by omega) (by omega) hj hA').1
    have h2 := he j hj
    rw [hcast]
    push_cast at h1 h2
    have hpos : (0 : ℝ) < ((C₁ : ℝ) + 1) * ((m' : ℝ) + 2) ^ 2 := by positivity
    have hq : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) ^ 2 := by positivity
    constructor <;> linarith
  have hKc : (0 : ℂ) ∉ ({D'} : Set ℂ) := fun h => hD' (Set.mem_singleton_iff.mp h).symm
  obtain ⟨Cst, hCst⟩ := hU p m' β hβ σ d hd e (((C₁ : ℝ) + 1) * ((m' : ℝ) + 2) ^ 2)
    (by nlinarith [sq_nonneg ((m' : ℝ) + 2)]) hexp {D'} isCompact_singleton hKc
  have hrem := hCst M.V Φ0 K hdec
  set Φ := U.PhiTop β σ d Φ0
  set S := G.rootSet (m' + 2) ((-1) ^ (m' + 3) * D')

  have hm2 : ((m' : ℂ) + 2) ≠ 0 := by
    have : ((m' + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' + 2 ≠ 0 by omega)
    simpa using this
  have hw : Function.Injective (fun j : Fin S.card => ((m' : ℂ) + 2) * (S.equivFin.symm j : ℂ)) := by
    intro j₁ j₂ h
    have h' := mul_left_cancel₀ hm2 h
    exact S.equivFin.symm.injective (Subtype.ext h')
  have hbd : ∀ x : ℂ, 1 + δ⁻¹ ≤ ‖x‖ →
      P (∑ j : Fin S.card, G.psi β ((((m' : ℂ) + 2) * (S.equivFin.symm j : ℂ)) * x) •
          ((((m' : ℂ) + 2)⁻¹ * ((‖(S.equivFin.symm j : ℂ)‖ ^ ((m' + 1) ^ 2) : ℝ) : ℂ)) •
            G.OmLong β (m' + 1) Φ (S.equivFin.symm j : ℂ))) ≤ (Cp * (Cst * K)) / ‖x‖ := by
    intro x hx
    have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
    have hxt : ‖x⁻¹‖ < δ := by rw [norm_inv]; exact inv_lt_of_inv_lt₀ hδ (by linarith)
    rw [← mainTerm_inv]
    have hc : (D' * x ^ (m' + 1)) * x⁻¹ ^ (m' + 1) = D' := by
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), mul_one]
    have h1 := hrem x⁻¹ (D' * x ^ (m' + 1)) (inv_ne_zero hx0) (by rw [hc]; exact Set.mem_singleton _)
    have h0 := hlow x⁻¹ (D' * x ^ (m' + 1)) (inv_ne_zero hx0) hxt hc
    have hsplit : G.mainTerm β m' (fun _ => 1) Φ x⁻¹ D' =
        ((‖x⁻¹‖ ^ ((m' + 1) ^ 2) : ℝ) : ℂ) • G.OmBlock β (m' + 1) Φ x⁻¹ (D' * x ^ (m' + 1)) -
          G.remainder β m' (fun _ => 1) Φ x⁻¹ (D' * x ^ (m' + 1)) := by
      unfold G.remainder; rw [hc]; abel
    rw [hsplit]
    calc P (((‖x⁻¹‖ ^ ((m' + 1) ^ 2) : ℝ) : ℂ) • G.OmBlock β (m' + 1) Φ x⁻¹ (D' * x ^ (m' + 1)) -
          G.remainder β m' (fun _ => 1) Φ x⁻¹ (D' * x ^ (m' + 1)))
        ≤ P (((‖x⁻¹‖ ^ ((m' + 1) ^ 2) : ℝ) : ℂ) • G.OmBlock β (m' + 1) Φ x⁻¹ (D' * x ^ (m' + 1))) +
          P (G.remainder β m' (fun _ => 1) Φ x⁻¹ (D' * x ^ (m' + 1))) := map_sub_le_add P _ _
      _ = P (G.remainder β m' (fun _ => 1) Φ x⁻¹ (D' * x ^ (m' + 1))) := by
          rw [map_smul_eq_mul, h0, mul_zero, zero_add]
      _ ≤ Cp * ‖G.remainder β m' (fun _ => 1) Φ x⁻¹ (D' * x ^ (m' + 1))‖ := hP _
      _ ≤ Cp * (Cst * K * ‖x⁻¹‖) := mul_le_mul_of_nonneg_left h1 hCp
      _ = (Cp * (Cst * K)) / ‖x‖ := by rw [norm_inv, div_eq_mul_inv]; ring
  have hzero := hAv β hβ M.V P S.card _ _ (Cp * (Cst * K)) (1 + δ⁻¹) hw hbd

  have hz0 : z₀ ≠ 0 := by
    intro h0
    have hm := hz₀
    simp only [S, G.rootSet, Multiset.mem_toFinset] at hm
    rw [Polynomial.mem_nthRoots (by omega), h0, zero_pow (by omega)] at hm
    have : D' = 0 := by
      have h3 : ((-1 : ℂ) ^ (m' + 3)) ≠ 0 := pow_ne_zero _ (by norm_num)
      exact (mul_eq_zero.mp hm.symm).resolve_left h3
    exact hD' this
  have hj := hzero (S.equivFin ⟨z₀, hz₀⟩)
  simp only [Equiv.symm_apply_apply, map_smul_eq_mul] at hj
  apply hslice
  rcases mul_eq_zero.mp hj with h | h
  · exfalso
    have hnz : ((m' : ℂ) + 2)⁻¹ * ((‖z₀‖ ^ ((m' + 1) ^ 2) : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero (inv_ne_zero hm2) ?_
      exact_mod_cast pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
    exact hnz (norm_eq_zero.mp h)
  · exact h

end PI.UnitaryGroupMassFormula.DLm
