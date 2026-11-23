import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentExpInjectiveCommutingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentExpLogSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentMatrixPowDimEqZeroStatement

namespace GlobalTheory.UnipotentLog

noncomputable def lg (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ j ∈ Finset.range d, ((-1 : ℚ) ^ j / ((j : ℚ) + 1)) • X ^ (j + 1)

theorem commute_lg {d : ℕ} {X Y : Matrix (Fin d) (Fin d) ℂ} (h : Commute X Y) :
    Commute (lg d X) (lg d Y) := by
  unfold lg
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  exact ((h.pow_pow _ _).smul_left _).smul_right _

theorem isNilpotent_lg {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (h : IsNilpotent X) :
    IsNilpotent (lg d X) := by
  unfold lg
  refine Commute.isNilpotent_sum (fun j _ => (h.pow_succ j).smul _) fun i j _ _ => ?_
  exact (((Commute.refl X).pow_pow _ _).smul_left _).smul_right _

theorem continuous_lg (d : ℕ) : Continuous (lg d) := by
  unfold lg
  refine continuous_finset_sum _ fun j _ => ?_
  exact (continuous_pow (M := Matrix (Fin d) (Fin d) ℂ) (j + 1)).const_smul
    ((-1 : ℚ) ^ j / ((j : ℚ) + 1))

theorem lg_zero (d : ℕ) : lg d 0 = 0 := by
  simp [lg]

theorem exp_lg {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (h : IsNilpotent X) :
    IsNilpotent.exp (lg d X) = 1 + X :=
  GlobalTheory.T.nilpotent_exp_log_series _ d X (GlobalTheory.T.nilpotent_matrix_pow_dim_eq_zero d X h)

theorem main : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (L : G → ℂ), (∀ φ : G → ℂ, Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) → (∀ γ ∈ H, φ γ = 0) → ∃ A : ℂ, ∀ t, φ t = A * L t) → ∀ (d : ℕ) (u : G →* Matrix (Fin d) (Fin d) ℂ), (∀ s, IsNilpotent (u s - 1)) → (∀ γ ∈ H, u γ = 1) → (∀ i j, Continuous fun s => u s i j) → ∃ (K : ℕ) (M : ℕ → Matrix (Fin d) (Fin d) ℂ), ∀ s, u s = ∑ k ∈ Finset.range K, L s ^ k • M k := by
  intro G _ _ H L hL d u hn hH hc
  set N : G → Matrix (Fin d) (Fin d) ℂ := fun s => lg d (u s - 1) with hN
  have hexp : ∀ s, IsNilpotent.exp (N s) = u s := fun s => by
    rw [hN]; simp only; rw [exp_lg (hn s)]; abel
  have hnil : ∀ s, IsNilpotent (N s) := fun s => isNilpotent_lg (hn s)
  have hcomm : ∀ s t, Commute (N s) (N t) := fun s t => by
    have h : Commute (u s) (u t) := (Commute.all s t).map u
    exact commute_lg ((h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _))
  have hadd : ∀ s t, N (s * t) = N s + N t := fun s t => by
    refine GlobalTheory.T.nilpotent_exp_injective_commuting _ _ _ ((hcomm _ _).add_right (hcomm _ _)) (hnil _)
      ((hcomm s t).isNilpotent_add (hnil s) (hnil t)) ?_
    rw [IsNilpotent.exp_add_of_commute (hcomm s t) (hnil s) (hnil t), hexp, hexp, hexp, map_mul]
  have hu : Continuous fun s => u s := continuous_matrix hc
  have hNc : Continuous N := (continuous_lg d).comp (hu.sub continuous_const)
  have hent : ∀ i j, ∃ A : ℂ, ∀ t, N t i j = A * L t := fun i j =>
    hL (fun t => N t i j) (hNc.matrix_elem i j) (fun s t => by simp [hadd])
      (fun γ hγ => by simp [hN, hH γ hγ, lg_zero])
  choose A hA using hent
  have hNs : ∀ s, N s = L s • Matrix.of A := fun s => by
    ext i j
    simp [hA, mul_comm]
  refine ⟨d, fun k => (k.factorial : ℚ)⁻¹ • (Matrix.of A) ^ k, fun s => ?_⟩
  rw [← hexp, IsNilpotent.exp_eq_sum (GlobalTheory.T.nilpotent_matrix_pow_dim_eq_zero d _ (hnil s)), hNs]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, smul_comm]

end GlobalTheory.UnipotentLog
