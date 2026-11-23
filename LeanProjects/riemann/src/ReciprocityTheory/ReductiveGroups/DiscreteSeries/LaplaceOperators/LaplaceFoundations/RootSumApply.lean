import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

section Wt

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem dgk_unit (t : Fin k → ℝ) : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := (dgk_mem t).1

theorem wt_full (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T)
      (fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) x := by
  intro θ _
  change HW.torepSig T (dg θ) x = _
  rw [dg_split, torep_mul T (kE_mem_Kset hε (dgk_unit _)) (dg_mem _), spanW_scalar T hε θ hx, map_smul]
  have h1 : HW.torepSig T (kE k r (dgk (th1 θ))) x =
      Complex.exp (((∑ q, μ q * th1 θ q : ℝ) : ℂ) * Complex.I) • x := hμ (th1 θ) (dgk_mem _)
  rw [h1, smul_smul, ← Complex.exp_add]
  congr 1
  have hs : (∑ a, (if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) * θ a) =
      (∑ a, Λ a * th2 θ a) + ∑ q, μ q * th1 θ q := by
    have e : ∑ q, μ q * th1 θ q = ∑ a : Fin (2 * r + k + 1), (if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0) := by
      rw [sumF' (k := k) (r := r) (fun a : Fin (2 * r + k + 1) => if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0)
        (fun p hp => by rw [dif_neg hp])]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : (fI k r q).val < k := q.2
      rw [dif_pos hq]
      rfl
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < k
    · simp [th2, ha]
    · simp [th2, ha]
  rw [hs, Complex.ofReal_add, add_mul]

theorem root_sum_apply {m : ℕ} (c : Fin m → Fin m → ℕ) (x : Fin m) :
    (∑ a, ∑ b, (c a b : ℝ) • (Pi.single a (1 : ℝ) - Pi.single b 1 : Fin m → ℝ)) x =
      ∑ b, (c x b : ℝ) - ∑ a, (c a x : ℝ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq]

theorem wt_cdom (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) (hx0 : x ≠ 0) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.CDom (Formalism.MainNotions.S.allPos k) μ (fun q => Λ (fI k r q)) := by
  have hfull := wt_full T hε hx hμ
  obtain ⟨c, hc, he⟩ := HW.KType.weight_le T hx0 (HW.torep_dτ_of_wt T hfull)
  have he' : ∀ y, (Λ - fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) y =
      ∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ) := by
    intro y
    rw [he]
    exact root_sum_apply c y

  have hzero : ∀ a b : Fin (2 * r + k + 1), a.val < k → ¬ b.val < k → c a b = 0 := by
    let g : Fin (2 * r + k + 1) → ℝ := fun y => if y.val < k then 0 else 1
    have hsum : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y.val < k
      · simp [g, hy]
      · rw [← he' y]; simp [g, hy]
    have hsum2 : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) =
        ∑ a, ∑ b, (c a b : ℝ) * (g a - g b) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hsum2] at hsum
    have hnp : ∀ a b : Fin (2 * r + k + 1), (c a b : ℝ) * (g a - g b) ≤ 0 := by
      intro a b
      by_cases h0 : c a b = 0
      · simp [h0]
      · have hab := (hc a b h0).1
        have hab' : a.val < b.val := hab
        refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
        simp only [g]
        split_ifs with h1 h2 h2 <;> norm_num
        omega
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hnp a b)).1 hsum
    intro a b ha hb
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hnp a b)).1 (hall a (Finset.mem_univ _)) b
      (Finset.mem_univ _)
    simp only [g, if_pos ha, if_neg hb] at h1
    norm_num at h1
    exact_mod_cast h1
  refine ⟨fun q q' => c (fI k r q) (fI k r q'), fun q q' h => ⟨?_, rfl⟩, ?_⟩
  · have := (hc _ _ h).1
    exact this
  · funext q
    have hq : (fI k r q).val < k := q.2
    have h1 := he' (fI k r q)
    simp only [Pi.sub_apply, dif_pos hq] at h1
    have e1 : ∑ b, (c (fI k r q) b : ℝ) = ∑ q', (c (fI k r q) (fI k r q') : ℝ) :=
      sumF' _ (fun p hp => by rw [hzero _ _ hq hp]; simp)
    have e2 : ∑ a, (c a (fI k r q) : ℝ) = ∑ q', (c (fI k r q') (fI k r q) : ℝ) := by
      refine sumF' _ (fun p hp => ?_)
      by_cases h0 : c p (fI k r q) = 0
      · simp [h0]
      · have := (hc _ _ h0).1
        have : p.val < (fI k r q).val := this
        exact absurd (lt_trans this hq) hp
    rw [e1, e2] at h1
    have e3 : (⟨(fI k r q).val, hq⟩ : Fin k) = q := Fin.ext rfl
    rw [e3] at h1
    rw [show ((fun q => Λ (fI k r q)) - μ) q = Λ (fI k r q) - μ q from rfl, h1]
    have := root_sum_apply (fun q q' => c (fI k r q) (fI k r q')) q
    rw [← this]
    rfl

end Wt

section Irr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

theorem kE_dgk (t : Fin k → ℝ) :
    kE k r (dgk t) = dg (fun a : Fin (2 * r + k + 1) => if h : a.val < k then t ⟨a.val, h⟩ else 0) := by
  ext i j
  simp only [dg, Matrix.diagonal_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dgk, dif_pos hi, dif_pos hj, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp [show i ≠ j by rintro rfl; exact hj hi]
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

theorem kE_cont : Continuous (kE k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kE]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem w_wtK : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
    (fun q => Λ (fI k r q)) T.w := by
  intro t _
  change HW.torepSig T (kE k r (dgk t)) T.w = _
  rw [kE_dgk]
  unfold dg
  rw [HW.torep_wt_w T _ (dg_mem _)]
  congr 3
  congr 1
  refine (sumF' (M := ℝ) (k := k) (r := r) _ (fun p hp => ?_)).trans (Finset.sum_congr rfl fun q _ => ?_)
  · simp [hp]
  · have hq : (fI k r q).val < k := q.2
    simp only [dif_pos hq]
    rfl

theorem rhoK_one (v : T.V) : rhoK (k := k) (r := r) T 1 v = v := by
  unfold rhoK
  rw [kE_one, (HW.torep_isURepOn T).1.1]
  rfl

theorem rhoK_mul (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a b : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) :
    rhoK (k := k) (r := r) T (a * b) v = rhoK (k := k) (r := r) T a (rhoK (k := k) (r := r) T b v) := by
  unfold rhoK
  rw [kE_mul, torep_mul T (kE_mem_Kset hε ha) (kE_mem_Kset hε hb)]

theorem rhoK_norm (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) : ‖rhoK (k := k) (r := r) T a v‖ = ‖v‖ :=
  (HW.torep_isURepOn T).2.1 _ (kE_mem_Kset hε ha) v

theorem rhoK_adj (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) (u v : T.V) :
    ⟪u, rhoK (k := k) (r := r) T h v⟫_ℂ = ⟪rhoK (k := k) (r := r) T (star h) u, v⟫_ℂ := by
  have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
  have hinv : rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v) = v := by
    rw [← rhoK_mul T hε hs hh, Unitary.star_mul_self_of_mem hh, rhoK_one]
  let Lm : T.V →ₗᵢ[ℂ] T.V :=
    { toLinearMap := (rhoK (k := k) (r := r) T (star h) : T.V →ₗ[ℂ] T.V), norm_map' := rhoK_norm T hε hs }
  have := Lm.inner_map_map u (rhoK (k := k) (r := r) T h v)
  change ⟪rhoK (k := k) (r := r) T (star h) u, rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v)⟫_ℂ = _
    at this
  rw [hinv] at this
  exact this.symm

theorem spanW_irred (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (S' : Submodule ℂ T.V)
    (hle : S' ≤ spanW (k := k) (r := r) T)
    (hS' : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S', rhoK (k := k) (r := r) T h v ∈ S') :
    S' = ⊥ ∨ spanW (k := k) (r := r) T ≤ S' := by
  have hperp : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'ᗮ, rhoK (k := k) (r := r) T h v ∈ S'ᗮ := by
    intro h hh v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    rw [rhoK_adj T hε hh]
    exact hv _ (hS' _ (Unitary.star_mem hh) u hu)
  have hbot : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ S' ⊓ S'ᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  obtain ⟨p, hp, q, hq, hpq⟩ := S'.exists_add_mem_mem_orthogonal T.w
  have hpw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) p := by
    intro t ht
    have hu : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := ht.1
    have h1 := w_wtK T t ht
    set c := Complex.exp (((∑ a, Λ (fI k r a) * t a : ℝ) : ℂ) * Complex.I)
    change rhoK (k := k) (r := r) T (dgk t) T.w = c • T.w at h1
    change rhoK (k := k) (r := r) T (dgk t) p = c • p
    rw [hpq, map_add, smul_add] at h1
    have hA : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S' := S'.sub_mem (hS' _ hu _ hp) (S'.smul_mem _ hp)
    have hB : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S'ᗮ := by
      have e : rhoK (k := k) (r := r) T (dgk t) p - c • p = c • q - rhoK (k := k) (r := r) T (dgk t) q := by
        rw [sub_eq_sub_iff_add_eq_add, h1]
        exact add_comm _ _
      rw [e]
      exact S'ᗮ.sub_mem (S'ᗮ.smul_mem _ hq) (hperp _ hu _ hq)
    exact sub_eq_zero.1 (hbot _ hA hB)
  have hqw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) q := by
    intro t ht
    have h1 := w_wtK T t ht
    have h2 := hpw t ht
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e, map_sub, h1, h2, smul_sub]
  have hpS : p ∈ spanW (k := k) (r := r) T := hle hp
  have hqS : q ∈ spanW (k := k) (r := r) T := by
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e]; exact sub_mem (w_mem_spanW T) hpS
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  have hp2 := wt_full T hε hpS hpw
  have hq2 := wt_full T hε hqS hqw
  rw [hfix] at hp2 hq2
  obtain ⟨a, ha⟩ := eq_smul_highestWeight_of_isWeight T hp2
  obtain ⟨b, hb⟩ := eq_smul_highestWeight_of_isWeight T hq2
  have hinner : ⟪p, q⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  rw [ha, hb, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, T.w_norm] at hinner
  simp only [RCLike.ofReal_one, one_pow, mul_one] at hinner
  rcases mul_eq_zero.1 hinner with h | h
  · left
    have ha0 : a = 0 := by simpa using h
    have hq' : T.w = q := by rw [hpq, ha, ha0, zero_smul, zero_add]
    have hle' : spanW (k := k) (r := r) T ≤ S'ᗮ := spanW_le T (hq' ▸ hq) hperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hbot x hx (hle' (hle hx))
  · right
    have hp' : T.w = p := by rw [hpq, hb, h, zero_smul, add_zero]
    exact spanW_le T (hp' ▸ hp) hS'

end Irr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
