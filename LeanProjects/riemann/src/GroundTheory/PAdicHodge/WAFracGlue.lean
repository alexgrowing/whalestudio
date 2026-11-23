import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigen
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

theorem exists_fixed_of_approx (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ) (U : ℕ → Fin n → T.RobbaExt ρ)
    (hU1 : SeqCauchy U (topRad ρ)) (hU2 : SeqCauchy U (F.radPow ρ))
    (hsmall : SeqSmall (fun J => twistDiff (F := F) A N (U J)) (topRad (F.powRadius ρ))) :
    ∃ g : Fin n → T.RobbaExt ρ, (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ i,
        T.extNorm ρ (topRad ρ) (g i - U J i) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g i - U J i) ≤ ε) ∧
      twistDiff (F := F) A N g = 0 := by

  set x : (t : ℕ) → ℕ → Fin n → T.RobbaExt (F.radSeq ρ t) := fun t J => F.phiIter A N (U J) t
    with hxdef
  have hCt : ∀ t, SeqCauchy (x t) (topRad _) ∧
      SeqCauchy (x t) ⟨F.radSeq ρ (t + 1), (F.radSeq ρ (t + 1)).2.1, F.radSeq_succ_le ρ t⟩ := by
    intro t
    induction t with
    | zero => exact ⟨hU1, hU2⟩
    | succ t ih =>
      exact ⟨ih.1.twistFrob A N (F.radSeq_le ρ (t + 1)), ih.2.twistFrob A N (F.radSeq_le ρ (t + 1))⟩
  have hDt : ∀ t, SeqSmall (fun J => x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i))
      (topRad (F.radSeq ρ (t + 1))) := by
    intro t
    induction t with
    | zero =>
      intro ε hε
      obtain ⟨J₀, hJ₀⟩ := hsmall ε hε
      refine ⟨J₀, fun J hJ i => ?_⟩
      change T.extNorm _ _ (twistDiff (F := F) A N (U J) i) ≤ ε
      exact hJ₀ J hJ i
    | succ t ih =>
      have h := SeqSmall.twistFrob A N (F.radSeq_le ρ (t + 2)) ih
      refine fun ε hε => (h ε hε).imp fun J₀ hJ₀ J hJ i => ?_
      have e1 : (x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) =
          F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
            (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) := by
        have h2 := twistFrob_res A N (F.radSeq_succ_le ρ t) (F.radSeq_le ρ (t + 1))
          (F.radSeq_le ρ (t + 2)) (x t J)
        have h3 : F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2)) (x (t + 1) J) -
              F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
                (fun j => T.res (F.radSeq_succ_le ρ t) (x t J j)) =
            F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
              (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) :=
          (twistFrob_sub A N (F.radSeq_le ρ (t + 2)) _ _).symm
        rw [← h3]
        exact congrArg₂ (· - ·) rfl h2.symm
      show T.extNorm _ (topRad (F.radSeq ρ (t + 2)))
        ((x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) i) ≤ ε
      rw [e1]
      exact hJ₀ J hJ i

  have hglue : ∀ i, ∃ g : T.RobbaExt ρ, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm ρ (topRad ρ) (g - U J i) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g - U J i) ≤ ε := by
    intro i
    refine exists_glue (F.radSeq ρ) (F.radSeq_succ_le ρ) (F.tendsto_radSeq ha ρ)
      (fun t J => x t J i) (fun t ε hε => ?_) (fun t ε hε => ?_)
    · obtain ⟨J₁, h1⟩ := (hCt t).1 ε hε
      obtain ⟨J₂, h2⟩ := (hCt t).2 ε hε
      exact ⟨max J₁ J₂, fun J hJ K hK => ⟨h1 J (le_of_max_le_left hJ) K (le_of_max_le_left hK) i,
        h2 J (le_of_max_le_right hJ) K (le_of_max_le_right hK) i⟩⟩
    · obtain ⟨J₀, h⟩ := hDt t ε hε
      refine ⟨J₀, fun J hJ => ?_⟩
      have := h J hJ i
      rw [← extNorm_neg, neg_sub]
      exact this
  choose g hg using hglue
  refine ⟨g, fun ε hε => ?_, ?_⟩
  ·
    choose J₀ hJ₀ using fun i => hg i ε hε
    exact ⟨Finset.univ.sup J₀, fun J hJ i =>
      hJ₀ i J ((Finset.le_sup (Finset.mem_univ i)).trans hJ)⟩
  ·
    funext i
    rw [Pi.zero_apply]
    apply (T.extNorm_eq_zero_iff (topRad _)).1
    have key : ∀ ε > 0, T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hsm⟩ := twistFrob_small A N (F.powRadius_le_self ρ) (topRad ρ) hε
      have hev : ∀ j, ∀ᶠ J in atTop, T.extNorm ρ (topRad ρ) (g j - U J j) ≤ δ := fun j => by
        obtain ⟨J₀, h⟩ := hg j δ hδ
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).1⟩
      have hev2 : ∀ᶠ J in atTop, T.extNorm ρ (F.radPow ρ) (g i - U J i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hg i ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).2⟩
      have hev3 : ∀ᶠ J in atTop, T.extNorm _ (topRad _) (twistDiff (F := F) A N (U J) i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hsmall ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => h J hJ i⟩
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := ((Filter.eventually_all.2 hev).and (hev2.and hev3)).exists
      have h1 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i +
            F.twistFrob A N ρ (F.powRadius_le_self ρ) (U J) i := by
        rw [twistFrob_sub, Pi.sub_apply, sub_add_cancel]
      simp only [twistDiff, Pi.sub_apply] at hJ3 ⊢
      have e2 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i - T.res (F.powRadius_le_self ρ) (g i) =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i +
            (F.twistFrob A N ρ (F.powRadius_le_self ρ) (U J) i - T.res (F.powRadius_le_self ρ) (U J i)) +
            -T.res (F.powRadius_le_self ρ) (g i - U J i) := by
        rw [h1, map_sub]; ring
      rw [e2]
      refine (extNorm_add_add_le_max _ _ _ _).trans (max_le (hsm (g - U J) (fun j => hJ1 j) i)
        (max_le hJ3 ?_))
      rw [extNorm_neg, extNorm_res]
      exact hJ2
    have h0 := T.extNorm_nonneg (topRad (F.powRadius ρ)) (twistDiff (F := F) A N g i)
    by_contra hne
    have hpos : 0 < T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) :=
      lt_of_le_of_ne h0 (Ne.symm hne)
    linarith [key _ (half_pos hpos)]

theorem twistDiff_one_apply {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ) (w : Fin 1 → T.RobbaExt ρ) :
    twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N w 0 =
      T.piInvE (F.powRadius ρ) ^ N * F.extFrob ρ (w 0) - T.res (F.powRadius_le_self ρ) (w 0) := by
  simp [twistDiff, twistFrob, Matrix.one_apply]

theorem extFrob_sub_eq_piE_pow_mul {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ) (w : T.RobbaExt ρ) :
    F.extFrob ρ w - T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) w =
      T.piE (F.powRadius ρ) ^ N *
        (T.piInvE (F.powRadius ρ) ^ N * F.extFrob ρ w - T.res (F.powRadius_le_self ρ) w) := by
  have h := T.piE_mul_piInvE (F.powRadius ρ)
  have h' : T.piE (F.powRadius ρ) ^ N * T.piInvE (F.powRadius ρ) ^ N = 1 := by
    rw [← mul_pow, h, one_pow]
  linear_combination (F.extFrob ρ w) * h'.symm

theorem exists_eigen_of_approx (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1} (N : ℕ)
    (u : ℕ → T.RobbaExt ρ)
    (hu1 : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, T.extNorm ρ (topRad ρ) (u J - u K) ≤ ε)
    (hu2 : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, T.extNorm ρ (F.radPow ρ) (u J - u K) ≤ ε)
    (hsmall : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, T.extNorm (F.powRadius ρ) (topRad _)
      (F.extFrob ρ (u J) - T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) (u J)) ≤ ε) :
    ∃ g : T.RobbaExt ρ, (∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
        T.extNorm ρ (topRad ρ) (g - u J) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g - u J) ≤ ε) ∧
      F.extFrob ρ g = T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) g := by
  set U : ℕ → Fin 1 → T.RobbaExt ρ := fun J _ => u J with hUdef
  set σ := F.powRadius ρ with hσ
  have hσ0 : (0 : ℝ) < σ := σ.2.1

  have hinv : T.extNorm σ (topRad σ) (T.piInvE σ ^ N) = ((σ : ℝ) ^ N)⁻¹ := by
    rw [extNorm_pow', extNorm_piInvE]
    simp [topRad, inv_pow]
  have hsm : SeqSmall (fun J => twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N (U J))
      (topRad σ) := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := hsmall ((σ : ℝ) ^ N * ε) (mul_pos (pow_pos hσ0 N) hε)
    refine ⟨J₀, fun J hJ i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show T.extNorm σ (topRad σ)
      (twistDiff (F := F) (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N (U J) 0) ≤ ε
    rw [twistDiff_one_apply]
    have e : T.piInvE σ ^ N * F.extFrob ρ (u J) - T.res (F.powRadius_le_self ρ) (u J) =
        T.piInvE σ ^ N * (F.extFrob ρ (u J) - T.piE σ ^ N * T.res (F.powRadius_le_self ρ) (u J)) := by
      have h := T.piE_mul_piInvE σ
      have h' : T.piInvE σ ^ N * T.piE σ ^ N = 1 := by rw [← mul_pow, mul_comm, h, one_pow]
      linear_combination (T.res (F.powRadius_le_self ρ) (u J)) * h'
    show T.extNorm σ (topRad σ) (T.piInvE σ ^ N * F.extFrob ρ (u J) -
      T.res (F.powRadius_le_self ρ) (u J)) ≤ ε
    rw [e, extNorm_mul, hinv]
    have h1 := hJ₀ J hJ
    calc ((σ : ℝ) ^ N)⁻¹ * T.extNorm σ (topRad σ)
          (F.extFrob ρ (u J) - T.piE σ ^ N * T.res (F.powRadius_le_self ρ) (u J))
        ≤ ((σ : ℝ) ^ N)⁻¹ * ((σ : ℝ) ^ N * ε) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (pow_nonneg hσ0.le N))
      _ = ε := by field_simp
  obtain ⟨g, hg, hfix⟩ := exists_fixed_of_approx ha (1 : Matrix (Fin 1) (Fin 1) (T.RobbaExt ρ)) N U
    (fun ε hε => (hu1 ε hε).imp fun J₀ h J hJ K hK _ => h J hJ K hK)
    (fun ε hε => (hu2 ε hε).imp fun J₀ h J hJ K hK _ => h J hJ K hK) hsm
  refine ⟨g 0, fun ε hε => (hg ε hε).imp fun J₀ h J hJ => h J hJ 0, ?_⟩
  have h0 := congrFun hfix 0
  rw [twistDiff_one_apply, Pi.zero_apply] at h0
  have e := extFrob_sub_eq_piE_pow_mul (F := F) N (g 0)
  rw [h0, mul_zero] at e
  exact sub_eq_zero.1 e

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
