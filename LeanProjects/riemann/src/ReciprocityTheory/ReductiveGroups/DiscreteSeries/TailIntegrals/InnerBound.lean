import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MpUnitary

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem cz0 {k : ℕ} (hk : 1 ≤ k) (z : Fin (2 * 0 + k + 1) → ℂ) (hT : 0 < Tz k 0 z) :
    herm (Hpk k 0) (epsV k 0) z ≠ 0 := by
  intro h
  have sgl : ∀ p : Fin (2 * 0 + k + 1), sg k 0 p.val = p.val := fun p => by
    have := p.2; unfold sg; rw [if_neg (by omega)]
  have hmv : ∀ (v : Fin (2 * 0 + k + 1) → ℂ) (p : Fin (2 * 0 + k + 1)),
      (Hpk k 0 *ᵥ v) p = (if p.val = 0 + k then -1 else 1) * v p := by
    intro v p; simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · rw [hpk_apply, sgl, if_pos rfl]
    · intro q _ hq; rw [hpk_apply, sgl, if_neg (fun e => hq (Fin.ext e)), zero_mul]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  have hw0 : (wI k 0 0).val = 0 := by simp [wI]
  have hwk : (wI k 0 (Fin.last k)).val = k := by simp [wI]
  have e1 : Hpk k 0 *ᵥ bvec (wI k 0 0) = bvec (wI k 0 0) := by
    funext p; rw [hmv]; split_ifs with hp
    · rw [bvec_ne _ _ (by omega), mul_zero]
    · rw [one_mul]
  have e2 : Hpk k 0 *ᵥ bvec (wI k 0 (Fin.last k)) = -bvec (wI k 0 (Fin.last k)) := by
    funext p; rw [hmv, Pi.neg_apply]; split_ifs with hp
    · rw [neg_one_mul]
    · rw [bvec_ne _ _ (by omega), mul_zero, neg_zero]
  have hh : herm (Hpk k 0) (epsV k 0) z =
      ((Real.sqrt 2)⁻¹ : ℂ) * (star (z (wI k 0 0)) - star (z (wI k 0 (Fin.last k)))) := by
    unfold epsV herm
    rw [mulVec_smul, mulVec_add, e1, e2, dotProduct_smul, dotProduct_add, dotProduct_neg, dot_bvec_r, dot_bvec_r,
      Pi.star_apply, Pi.star_apply, smul_eq_mul, sub_eq_add_neg]
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
    have : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by rw [sq2_mul_sq2_eq_half]; norm_num
    exact left_ne_zero_of_mul this
  rw [hh] at h
  have hzz : z (wI k 0 0) = z (wI k 0 (Fin.last k)) :=
    star_injective (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc))
  have hre : (herm (Hpk k 0) z z).re = ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    unfold herm
    simp only [dotProduct, hmv, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.star_apply]
    split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply]
  have hne : wI k 0 0 ≠ wI k 0 (Fin.last k) := fun e => by have := congrArg Fin.val e; omega
  have key : 0 ≤ ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (wI k 0 (Fin.last k))),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ (wI k 0 0)⟩)]
    rw [if_pos (show (wI k 0 (Fin.last k)).val = 0 + k by omega), if_neg (show ¬ (wI k 0 0).val = 0 + k by omega),
      hzz]
    have hrest : 0 ≤ ∑ p ∈ (Finset.univ.erase (wI k 0 (Fin.last k))).erase (wI k 0 0),
        (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpk : p ≠ wI k 0 (Fin.last k) := (Finset.mem_erase.1 (Finset.mem_erase.1 hp).2).1
      rw [if_neg (show ¬ (p.val = 0 + k) from fun e => hpk (Fin.ext (by omega)))]
      exact mul_nonneg zero_le_one (Complex.normSq_nonneg _)
    linarith
  unfold Tz at hT
  rw [hre] at hT
  linarith

theorem cz_ne {k n : ℕ} (hk : 1 ≤ k) (z1 : Fin (2 * n + k + 1) → ℂ) (hT : 0 < Tz k n z1) :
    herm (Hpk k n) (phiV k n ⟨0, by omega⟩) (fvec k n z1 ⟨0, by omega⟩) ≠ 0 := by
  by_cases hn : 0 < n
  · unfold phiV fvec
    rw [dif_pos hn, dif_pos hn, herm_bb, hpk_apply]
    rw [if_pos (show (esI k n ⟨0, hn⟩).val = sg k n (eI k n ⟨0, hn⟩).val by
        show 2 * n + k - 0 = sg k n 0; unfold sg; rw [if_pos (Or.inl hn)]),
      if_neg (show ¬ (eI k n ⟨0, hn⟩).val = n + k by show ¬ 0 = n + k; omega)]
    norm_num
  · have hn0 : n = 0 := by omega
    subst hn0
    unfold phiV fvec
    rw [dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0)]
    exact cz0 hk z1 hT

def etaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w

def eta'F (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w

def zetaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (k - 1) → ℂ := fun i => herm (Hpk k n) (wv k n i) w

theorem herm_linF' {k n : ℕ} (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (etaF k n w) (eta'F k n w) (zetaF k n w) (hcoord k n (y, s)) :=
  herm_linF k n hk y w s

section inner
variable {k r' : ℕ}

theorem inner_bound (hIW : IW) (hF : FormulaF) (hHC : HeisConjLev) (hHA : HeisAct) (hk : 1 ≤ k)
    (s : Fin (1 + r' + 1) → ℝ) (δ γ C : ℝ) (z1 : Fin (2 * r' + k + 1) → ℂ)
    (hC : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)))
    (hcz : herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) ≠ 0)
    (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∫⁻ X : HPar k r', ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m) *
          ENNReal.ofReal ((1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
  obtain ⟨κ, hκG, hκU, t, ht, htn, hD⟩ := lev_data hIW hHC hk m hm
  have hκU' : κ * κᴴ = 1 := mul_eq_one_comm.1 hκU
  have h00 : (0 : Fin (r' + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have ht' : m *ᵥ phiV k r' ⟨0, by omega⟩ = t • (κ *ᵥ phiV k r' ⟨0, by omega⟩) := by rw [← h00]; exact ht
  obtain ⟨w, hw⟩ : ∃ w, w = κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∏ a : Fin (r' + 1), Del k r' a m ^ (-s (su a)) := ⟨_, rfl⟩
  have hDel : ∀ (n : ℕ) (l : Fin (n + 1)) (x : Mat k n), 0 ≤ Del k n l x := fun n l x => Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hpt : ∀ X : HPar k r',
      ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) =
      ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
        (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := by
    intro X
    obtain ⟨hD0, hDS⟩ := hD X
    have hde : ∀ (x : Xp (1 + r') (k - 1)) (l : Fin (1 + r' + 1)), 0 ≤ de x l := fun x l => Real.sqrt_nonneg _
    have hmr : ∀ a : Fin (r' + 1), (Del k r' a m * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a)) ^ (-s (su a)) =
        Del k r' a m ^ (-s (su a)) * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a) ^ (-s (su a)) :=
      fun a => Real.mul_rpow (hDel _ _ _) (hde _ _)
    have hxi : xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m) =
        A * ∏ l, de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l) := by
      unfold xiR
      rw [prod_su, prod_su (fun l => de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l)), hD0]
      simp only [hDS, (hF k r' hk).1, hmr, Finset.prod_mul_distrib]
      rw [hA]; ring
    have hX : X.1 = κ *ᵥ (κᴴ *ᵥ X.1) := by rw [mulVec_mulVec, hκU', one_mulVec]
    have hmf : m *ᵥ fvec k r' z1 ⟨0, by omega⟩ = κ *ᵥ w := by rw [hw, mulVec_mulVec, hκU', one_mulVec]
    have hh : herm (Hpk k r') (κ *ᵥ w) X.1 = star (herm (Hpk k r') (κᴴ *ᵥ X.1) w) := by
      conv_lhs => rw [hX]
      rw [herm_UH _ _ hκG]
      exact (herm_conj _ (hpk_conjT k r') _ _).symm
    have hlam : lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
        2 * (linF (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (hcoord k r' (κᴴ *ᵥ X.1, X.2))).im + lam k r' z1 m := by
      rw [lam_lev hHA, hmf, hh, herm_linF' hk _ w X.2, Complex.star_def, Complex.conj_im]
      ring
    rw [hxi, hlam, ENNReal.ofReal_mul hA0, ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hde _ l) _)]
    unfold GI; rw [mul_assoc]
  have key : t * eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) := by
    show t * herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) w = _
    rw [hw, ← herm_UH _ _ hκG (phiV k r' ⟨0, by omega⟩) (κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩)),
      mulVec_mulVec (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) κ κᴴ, hκU', one_mulVec, ← herm_smul_l, ← ht', herm_UH _ _ hm]
  have ht0 : t ≠ 0 := fun h => hcz (by rw [← key, h, zero_mul])
  have hη0 : eta'F k r' w ⟨0, by omega⟩ ≠ 0 := fun h => hcz (by rw [← key, h, mul_zero])
  have hκH : (κᴴ)ᴴ * κᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hκU'
  have hg : Measurable (fun x => GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) (hcoord k r' x)) :=
    (meas_GI _ _ _ _ _ _).comp (hF k r' hk).2.measurable
  have hD0pos : 0 < Del k r' 0 m := by rw [← htn]; exact norm_pos_iff.2 ht0
  have hcz0 : 0 < ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ := norm_pos_iff.2 hcz
  have hnorm : ‖eta'F k r' w ⟨0, by omega⟩‖ =
      ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ / Del k r' 0 m := by
    have : eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) / t := by
      rw [eq_div_iff ht0, mul_comm]; exact key
    rw [this, norm_div, htn]
  have hQ : xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m = A * Del k r' 0 m ^ γ := by
    unfold xiR; rw [hA, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, sub_zero]
    rw [show -(s (su 0) - γ) = -s (su 0) + γ by ring, Real.rpow_add hD0pos]; ring
  have hQ0 : 0 ≤ xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m :=
    Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hR0 : 0 ≤ (1 + |lam k r' z1 m|) ^ (-(δ / 4)) := Real.rpow_nonneg (by positivity) _
  calc _ = ∫⁻ X : HPar k r', ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_congr hpt
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' X) := by rw [(mp_hpar κᴴ hκH).lintegral_comp hg]
    _ = ENNReal.ofReal A * ∫⁻ x, GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) x := by
          rw [(hF k r' hk).2.lintegral_comp (meas_GI _ _ _ _ _ _)]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4)) := by
          gcongr; exact hC _ _ _ _ hη0
    _ = ENNReal.ofReal (A * (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4))) :=
          (ENNReal.ofReal_mul hA0).symm
    _ = ENNReal.ofReal ((C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m * (1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
          congr 1
          rw [hnorm, Real.div_rpow hcz0.le hD0pos.le, Real.rpow_neg hD0pos.le, div_inv_eq_mul, hQ, neg_div]; ring
    _ = _ := by rw [ENNReal.ofReal_mul' (mul_nonneg hQ0 hR0), ENNReal.ofReal_mul hQ0]

end inner

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
