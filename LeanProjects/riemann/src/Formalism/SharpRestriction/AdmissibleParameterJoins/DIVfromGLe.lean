import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV

def RankHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧
    ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

def CountTie (D : D7) : Prop :=
  (∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u) ∧ D.what₂.Dstar = StandardLattice.DstarD D

theorem exp_logXuD (D : D7) (hT : CountTie D) (u : D.what₂.Word) :
    Real.exp (StandardLattice.logXuD D u) = (D.mem u).A.Xu := by
  obtain ⟨hT1, hT2⟩ := hT
  have hpos : 0 < (D.mem u).A.Dstar / ((D.mem u).A.duStar : ℝ) :=
    div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)
  unfold StandardLattice.logXuD StandardLattice.logXu
  rw [← hT1 u, ← hT2, ← D.Dstar_eq u]
  unfold Formalism.BasicNotions.ColumnsAtT.Xu
  rw [Real.rpow_def_of_pos hpos, mul_comm]

theorem rank_count_bound_of_data (D : D7) (L : SizeData₂ D) (Lv : LevelData D) (C0 C : ℝ) (Δ : ℝ)
    (h4 : StandardLattice.Conclusion4f D Lv) (h5c : StandardLattice.TorusPairsWithVariant D L.sc C0 C) (h5v : StandardLattice.VandermondeVariationBound D L.sc C0 C)
    (hB : StandardLattice.DataB D L.sc C0 Δ (fun j ρ => wSz D (j + 1) ρ))
    (hR : RankHyp D) (hT : CountTie D) (hWs : Formalism.MainNotions.SizeWords L) :
    LocalQuadraticParts.HerrExtensionClause L (max C (Real.exp C)) := by
  obtain ⟨hT1, hT2⟩ := hT
  obtain ⟨hG, hSp, hU⟩ := hR
  have hL : 0 < L.sc.L := by
    obtain ⟨hv, hlv, -⟩ := hB
    have hv1 : 1 < D.host.v := lt_of_lt_of_le (by linarith [Real.pi_gt_three]) hv
    linarith [Real.log_pos hv1]
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hCC : C ≤ max C (Real.exp C) := le_max_left _ _
  have hCe : Real.exp C ≤ max C (Real.exp C) := le_max_right _ _
  have hCpos : 0 < max C (Real.exp C) := lt_of_lt_of_le (Real.exp_pos C) hCe
  have hXu : ∀ u, Real.log (D.mem u).A.Xu = StandardLattice.logXuD D u := by
    intro u
    rw [← exp_logXuD D ⟨hT1, hT2⟩ u, Real.log_exp]
  unfold LocalQuadraticParts.HerrExtensionClause
  refine ⟨fun u => ?_, fun u u' => ?_, ?_⟩
  · have hΓ : 1 ≤ (D.mem u).A.GamP := le_of_lt (D.mem u).A.one_lt_gammaP
    have hGpos : 0 < (D.mem u).A.GamP := by linarith
    have hwin := D.T_win u
    have hlo : Real.exp (StandardLattice.logXuD D u) * (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) ≤
        ((D.mem u).A.T : ℝ) := by
      rw [exp_logXuD D ⟨hT1, hT2⟩ u]
      exact hwin.1
    have hhi : ((D.mem u).A.T : ℝ) ≤ Real.exp (StandardLattice.logXuD D u) *
        (D.mem u).A.GamP ^ (-(2 : ℝ) / (D.R.f * D.R.k)) * (1 + 1 / ((D.R.f : ℝ) * D.R.k)) := by
      rw [exp_logXuD D ⟨hT1, hT2⟩ u, mul_comm _ (1 + _)]
      exact hwin.2
    obtain ⟨h1, h2, h3⟩ := h5c Δ _ hB _ hΓ u hlo hhi
    have hrank : ((D.duS u : ℕ) : ℝ) =
        StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f :=
      h4 hG hSp u (hU u).1 (hU u).2
    have hTge : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := by
      have : 1 < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ (by linarith) (by omega)
      linarith
    have hdu : 0 < StandardLattice.duStarU D u := by
      rw [← hT1 u]
      exact_mod_cast (D.mem u).A.duStar_pos
    have hDs : (D.mem u).A.Dstar = StandardLattice.DstarD D := by rw [D.Dstar_eq u, hT2]
    have hDpos : 0 < StandardLattice.DstarD D := by
      rw [← hDs]
      exact (D.mem u).A.Dstar_pos
    have hQ : (D.duS u : ℝ) * (D.mem u).A.GamP ^ 2 / (D.mem u).A.Dstar =
        StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
          (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) := by
      rw [hrank, hDs, Real.rpow_neg hGpos.le, Real.rpow_two]
      field_simp
    have hQpos : 0 < StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) :=
      div_pos (mul_pos hdu (pow_pos hTk _)) (mul_pos hDpos (Real.rpow_pos_of_pos hGpos _))
    rw [abs_le] at h1
    have hQlo : Real.exp (-C) ≤ StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) := by
      rw [← Real.exp_log hQpos]
      exact Real.exp_le_exp.mpr h1.1
    have hQhi : StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f /
        (StandardLattice.DstarD D * (D.mem u).A.GamP ^ (-(2 : ℝ))) ≤ Real.exp C := by
      rw [← Real.exp_log hQpos]
      exact Real.exp_le_exp.mpr h1.2
    have hS : (∑ j ∈ SizeData₂.lifts D, (1 / (D.R.f : ℝ)) *
          ∑ ρ : D.what₂.Tau, Real.log (wSz D j ρ * D.host.v / Real.pi)) =
        ∑ j ∈ Finset.range D.R.m, (1 / (D.R.f : ℝ)) *
          ∑ ρ : D.what₂.Tau, Real.log (wSz D (j + 1) ρ * D.host.v / Real.pi) := by
      have himg : SizeData₂.lifts D = (Finset.range D.R.m).image (· + 1) := by
        ext j
        simp only [SizeData₂.lifts, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hj1, hj2⟩
          exact ⟨j - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩
          omega
      rw [himg, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    have hg : (∑ g ∈ L.gTypes, Real.log (g : ℝ)) ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
      rw [Fin.sum_univ_two]
      unfold SizeData₂.gTypes
      by_cases h : D.host.g 0 = D.host.g 1
      · rw [h]
        simp only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.sum_singleton]
        linarith [Real.log_natCast_nonneg (D.host.g 1)]
      · rw [Finset.sum_pair h]
    have hX : 0 ≤ L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k := by positivity
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc (max C (Real.exp C))⁻¹ ≤ (Real.exp C)⁻¹ := (inv_le_inv₀ hCpos (Real.exp_pos C)).mpr hCe
        _ = Real.exp (-C) := (Real.exp_neg C).symm
        _ ≤ _ := by rw [hQ]; exact hQlo
    · rw [hQ]
      exact le_trans hQhi hCe
    · calc Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * L.sc.L := h2
        _ ≤ max C (Real.exp C) * D.R.m * L.sc.L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hm) hL.le
    · unfold StandardLattice.lowB at h3
      rw [hS]
      nlinarith [mul_le_mul_of_nonneg_right hCC hX, mul_le_mul_of_nonneg_left hg hm]
  · rw [hXu, hXu]
    exact le_trans ((h5v Δ _ hB).2 u u')
      (mul_le_mul_of_nonneg_right hCC (Real.log_natCast_nonneg _))
  · have hW : Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3) := hWs
    exact le_trans hW (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem family_rank_count_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 : ℝ)
    (h4 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx i).lev)
    (h5 : StandardLattice.PartFiveFamilyBounds Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.SizeWords (Fm.L x i) ∧ RankHyp (Fm.D x i) ∧
      ∃ Δ : ℝ, StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ (fun j ρ => wSz (Fm.D x i) (j + 1) ρ)) :
    LocalQuadraticParts.CountFamily Fm := by
  obtain ⟨C, x5, hP⟩ := h5 C0
  obtain ⟨x0, hE⟩ := hE
  unfold LocalQuadraticParts.CountFamily
  refine ⟨max C (Real.exp C), max (max x0 x5) (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx5 : x5 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  obtain ⟨hWs, hR, Δ, hB⟩ := hE x hx0 i
  obtain ⟨-, h5c, h5v⟩ := hP x hx5 hx1 i
  exact rank_count_bound_of_data (Fm.D x i) (Fm.L x i) (Fm.ex x hx1 i).lev C0 C Δ (h4 x hx1 i) h5c h5v hB hR
    ⟨(Fm.ex x hx1 i).duStar_def, (Fm.ex x hx1 i).Dstar_def⟩ hWs

end Formalism.MainNotions.J
