import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.HasDerivAtCompLog

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

theorem det_eps : (((eps : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  simp [Matrix.det_fin_two_of]

theorem lT_map_eq_zero_of_pos (hσ : σ.IsIrreducible) {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    {ψ : ℝ → ℂ} (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {k : ℤ} {u : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (hu0 : u ≠ 0)
    (hWu : ∀ t, Wt σ l u t = 0) {g : FiltrationCocycleLiftCriterion}
    (hg : 0 < (((g : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det) :
    lT σ l (σ g u) = 0 := by
  obtain ⟨s, x, t, θ, rfl⟩ := exists_iwasawa g hg
  obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hk hu0 (zPos_mem_weightSpace σ hk s)
  have e : σ (zPos s * nMat x * aT t * kMat θ) u = σ (nMat x) (σ (aT t) ((chi k θ * c) • u)) := by
    have eg : zPos s * nMat x * aT t * kMat θ = nMat x * aT t * (zPos s * kMat θ) := by
      calc zPos s * nMat x * aT t * kMat θ = nMat x * (zPos s * aT t) * kMat θ := by
            rw [zPos_mul_comm s (nMat x), mul_assoc (nMat x)]
        _ = nMat x * (aT t * zPos s) * kMat θ := by rw [zPos_mul_comm s (aT t)]
        _ = nMat x * aT t * (zPos s * kMat θ) := by simp only [mul_assoc]
    rw [eg]
    simp only [UnitaryRep.map_mul_apply]
    rw [hk θ, map_smul, hc, smul_smul, mul_comm]
  have hsm : IsSm σ (σ (aT t) ((chi k θ * c) • u)) :=
    isSm_map σ ((hGL2.smoothVectors (πσ σ)).smul_mem _ hu) _
  rw [e, hW x _ hsm, map_smul, lT_smul (isSm_map σ hu _)]
  have : lT σ l (σ (aT t) u) = 0 := hWu t
  rw [this]; ring

theorem lT_map_eq_zero (hσ : σ.IsIrreducible) {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    {ψ : ℝ → ℂ} (hW : ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w)
    {k : ℤ} {u u' : H} (hu : IsSm σ u) (hk : u ∈ weightSpace σ k) (hu0 : u ≠ 0)
    (hu' : IsSm σ u') (hk' : u' ∈ weightSpace σ (-k)) (hu0' : u' ≠ 0)
    (hWu : ∀ t, Wt σ l u t = 0) (hWu' : ∀ t, Wt σ l u' t = 0) (g : FiltrationCocycleLiftCriterion) :
    lT σ l (σ g u) = 0 := by
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero ((g : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ)
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  ·
    obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hk' hu0' (eps_mem_weightSpace σ hk)
    have hge : 0 < ((((g * eps : FiltrationCocycleLiftCriterion) : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, det_eps]
      linarith
    have e : σ g u = σ (g * eps) (c • u') := by
      rw [← hc, ← UnitaryRep.map_mul_apply, mul_assoc, eps_mul_eps, mul_one]
    rw [e, map_smul, lT_smul (isSm_map σ hu' _),
      lT_map_eq_zero_of_pos hσ hW hu' hk' hu0' hWu' hge, mul_zero]
  · exact lT_map_eq_zero_of_pos hσ hW hu hk hu0 hWu hpos

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

def IsWhit (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w

omit [CompleteSpace H] in
theorem eq_zero_of_mem_bot {V : Submodule ℂ H} (hV : V = ⊥) {u : H} (hu : u ∈ V) : u = 0 := by
  rw [hV, Submodule.mem_bot] at hu; exact hu

theorem Wt_eq_zero_deriv {l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ}
    (hl : hGL2.IsSmoothContinuous (πσ σ) l) {u : H} (hu : IsSm σ u) (h0 : ∀ t, Wt σ l u t = 0)
    (t : ℝ) : Wt σ l (dπ σ lH u) t = 0 := by
  have h1 := hasDerivAt_Wt hl hu t
  have e : Wt σ l u = fun _ => 0 := funext h0
  rw [e] at h1
  exact h1.unique (hasDerivAt_const t 0)

theorem exists_weight_data (hσ : σ.IsIrreducible) {ψ : ℝ → ℂ} {θ : ℝ} (hθ : θ ≠ 0)
    (hψ : HasDerivAt ψ (I * θ) 0) :
    ∃ (j : ℤ) (v v' : H), IsSm σ v ∧ v ∈ weightSpace σ j ∧ v ≠ 0 ∧
      IsSm σ v' ∧ v' ∈ weightSpace σ (-j) ∧ v' ≠ 0 ∧
      ∀ l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ, hGL2.IsSmoothContinuous (πσ σ) l →
        IsWhit σ ψ l → (∀ t, Wt σ l v t = 0) → ∀ t, Wt σ l v' t = 0 := by
  have := hσ.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨j₁, hj₁⟩ := exists_wProj_ne_zero σ hx
  have hP : ∃ n : ℕ, ∃ j : ℤ, j.natAbs = n ∧ weightSpace σ j ≠ ⊥ :=
    ⟨j₁.natAbs, j₁, rfl, fun h => hj₁ (eq_zero_of_mem_bot h (wProj_mem σ j₁ x))⟩
  classical
  set n₀ := Nat.find hP with hn₀
  obtain ⟨j, hjn, hj⟩ := Nat.find_spec hP
  rw [← hn₀] at hjn
  have hmin : ∀ k : ℤ, k.natAbs < n₀ → weightSpace σ k = ⊥ := by
    intro k hk
    by_contra hne
    exact Nat.find_min hP hk ⟨k, rfl, hne⟩

  have hn₀ne : weightSpace σ (n₀ : ℤ) ≠ ⊥ := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [← hjn, ← hj']; exact hj
    · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hj
      rw [Submodule.ne_bot_iff]
      refine ⟨σ eps y, ?_, fun h => hy0 (σ.map_injective eps (by rw [h, map_zero]))⟩
      have := eps_mem_weightSpace σ hy
      rwa [hj', neg_neg, hjn] at this
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hn₀ne
  obtain ⟨v, hv, hv0, hvs⟩ := exists_smooth_weight σ hy hy0
  set v' := σ eps v with hv'def
  have hv'k : v' ∈ weightSpace σ (-(n₀ : ℤ)) := eps_mem_weightSpace σ hv
  have hv's : IsSm σ v' := isSm_map σ hvs eps
  have hv'0 : v' ≠ 0 := fun h => hv0 (σ.map_injective eps (by rw [← hv'def, h, map_zero]))

  have lowest : Lop σ v = 0 → ∃ (j : ℤ) (v v' : H), IsSm σ v ∧ v ∈ weightSpace σ j ∧ v ≠ 0 ∧
      IsSm σ v' ∧ v' ∈ weightSpace σ (-j) ∧ v' ≠ 0 ∧
      ∀ l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ, hGL2.IsSmoothContinuous (πσ σ) l →
        IsWhit σ ψ l → (∀ t, Wt σ l v t = 0) → ∀ t, Wt σ l v' t = 0 := by
    intro hL
    have hR : Rop σ v' = 0 := by rw [hv'def, ← map_eps_Lop hvs, hL, map_zero]
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · refine ⟨-(n₀ : ℤ), v', v, hv's, hv'k, hv'0, hvs, by rwa [neg_neg], hv0, fun l hl hW _ => ?_⟩
      exact Wt_eq_zero_of_Lop hl hneg hψ hW hvs hv hL
    · exact ⟨n₀, v, v', hvs, hv, hv0, hv's, hv'k, hv'0, fun l hl hW _ =>
        Wt_eq_zero_of_Rop hl hpos hψ hW hv's hv'k hR⟩
  rcases Nat.lt_or_ge n₀ 2 with hlt | hge
  · interval_cases hn : n₀
    ·
      refine ⟨0, v, v', hvs, by simpa using hv, hv0, hv's, by simpa using hv'k, hv'0,
        fun l hl hW h0 t => ?_⟩
      obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hv hv0 (by simpa using hv'k)
      rw [hc, Wt_smul hvs, h0, mul_zero]
    ·
      have hLv : Lop σ v ∈ weightSpace σ (-1) := by
        have := Lop_mem hvs hv; norm_num at this; exact this
      have hRv' : Rop σ v' ∈ weightSpace σ 1 := by
        have := Rop_mem hv's hv'k; norm_num at this; exact this
      have hv1 : v ∈ weightSpace σ 1 := by simpa using hv
      have hv'1 : v' ∈ weightSpace σ (-1) := by simpa using hv'k
      by_cases hR : Rop σ v' = 0
      · apply lowest
        obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hv'1 hv'0 hLv
        have hin : ⟪v', Lop σ v⟫_ℂ = 0 := by
          have := inner_Rop hv's hvs
          rw [hR, inner_zero_left] at this
          linear_combination this
        rw [hc, inner_smul_right] at hin
        have hc0 : c = 0 := (mul_eq_zero.1 hin).resolve_right (inner_self_ne_zero.2 hv'0)
        rw [hc, hc0, zero_smul]
      · have hLv0 : Lop σ v ≠ 0 := by
          intro hL
          apply hR
          obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hv1 hv0 hRv'
          have hin : ⟪Rop σ v', v⟫_ℂ = 0 := by
            rw [inner_Rop hv's hvs, hL, inner_zero_right, neg_zero]
          rw [hc, inner_smul_left] at hin
          have hc0 : c = 0 := by
            have := (mul_eq_zero.1 hin).resolve_right (inner_self_ne_zero.2 hv0)
            simpa using this
          rw [hc, hc0, zero_smul]
        obtain ⟨c, hc⟩ := weightSpace_eq_smul σ hσ hLv hLv0 hv'1
        refine ⟨1, v, v', hvs, hv1, hv0, hv's, hv'1, hv'0, fun l hl hW h0 t => ?_⟩
        have hpsi : HasDerivAt ψ (I * θ) 0 := hψ
        rw [hc, Wt_smul (isSm_Lop hvs), Wt_Lop hl hpsi hW hvs hv1, Wt_eq_zero_deriv hl hvs h0, h0]
        ring
  ·
    apply lowest
    have hLv := Lop_mem hvs hv
    have hbot : weightSpace σ ((n₀ : ℤ) - 2) = ⊥ := hmin _ (by omega)
    exact eq_zero_of_mem_bot hbot hLv

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

noncomputable def whitSpace (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) :
    Submodule ℂ (hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) where
  carrier := {l | ∀ (x : ℝ) (w : hGL2.SmoothFrechet (πσ σ)),
    l (hGL2.smoothOp (πσ σ) (nMat x) w) = ψ x * l w}
  add_mem' {a b} ha hb := fun x w => by
    show a _ + b _ = ψ x * (a w + b w)
    rw [ha x w, hb x w]; ring
  zero_mem' := fun x w => by
    show (0 : ℂ) = ψ x * 0
    ring
  smul_mem' c a ha := fun x w => by
    show c * a _ = ψ x * (c * a w)
    rw [ha x w]; ring

noncomputable def toLin (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ where
  toFun w := l w
  map_add' a b := l.map_add a b
  map_smul' c a := l.map_smul c a

theorem toLin_apply (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) (w : hGL2.smoothVectors (πσ σ)) :
    toLin l w = l w := rfl

theorem toLin_sub_smul (l l' : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) (r : ℂ) :
    toLin (l - r • l') = toLin l - r • toLin l' := by
  ext w; rfl

theorem isSmoothContinuous_toLin (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) :
    hGL2.IsSmoothContinuous (πσ σ) (toLin l) := by
  obtain ⟨s, C, h⟩ := hGL2.isSmoothContinuous_of_continuous (πσ σ) l
  exact ⟨s, C, h⟩

theorem isWhit_of_mem {ψ : ℝ → ℂ} {l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ}
    (hl : l ∈ whitSpace σ ψ) : IsWhit σ ψ (toLin l) := by
  intro x w hw
  rw [lT_of hw, lT_of (isSm_map σ hw _)]
  exact hl x ⟨w, hw⟩

theorem Wt_sub_smul {l₁ l₂ : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ} {u : H} (hu : IsSm σ u) (c : ℂ)
    (t : ℝ) : Wt σ (l₁ - c • l₂) u t = Wt σ l₁ u t - c * Wt σ l₂ u t := by
  simp only [Wt, lT_of (isSm_map σ hu _), LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

theorem deriv_char_eq {ψ : ℝ → ℂ} (hmul : ∀ x y, ψ (x + y) = ψ x * ψ y) (hnorm : ∀ x, ‖ψ x‖ = 1)
    (hne : ∃ x, ψ x ≠ 1) {β : ℂ} (hβ : HasDerivAt ψ β 0) :
    ∃ θ : ℝ, θ ≠ 0 ∧ β = I * θ := by
  have h0 : ψ 0 = 1 := by
    have e := hmul 0 0
    rw [add_zero] at e
    have hn : ψ 0 ≠ 0 := fun h => by have := hnorm 0; rw [h, norm_zero] at this; norm_num at this
    have : ψ 0 * (ψ 0 - 1) = 0 := by linear_combination -e
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hn
    · linear_combination h

  have hre : β.re = 0 := by
    have h1 := hβ.norm_sq
    have e : (fun x => ‖ψ x‖ ^ 2) = fun _ => (1 : ℝ) := funext fun x => by rw [hnorm x, one_pow]
    rw [e] at h1
    have h2 := h1.unique (hasDerivAt_const 0 (1 : ℝ))
    rw [h0, Complex.inner, map_one, mul_one] at h2
    linarith
  refine ⟨β.im, ?_, ?_⟩
  · intro him
    apply absurd hne
    push Not

    have hβ0 : β = 0 := Complex.ext hre him
    have hd : ∀ s, HasDerivAt ψ 0 s := by
      intro s
      have h1 : HasDerivAt (fun t => ψ s * ψ t) (ψ s * β) 0 := hβ.const_mul (ψ s)
      have e : (fun t => ψ s * ψ t) = fun t => ψ (s + t) := funext fun t => (hmul s t).symm
      rw [e, hβ0, mul_zero] at h1
      have h2 : HasDerivAt (fun t => ψ (s + t)) 0 (s - s) := by rw [sub_self]; exact h1
      have := h2.comp_sub_const s s
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      simp only
      rw [add_sub_cancel]
    intro x
    rw [← h0]
    exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) x 0
  · apply Complex.ext <;> simp [hre]

theorem exists_whitSpace_le_span (hσ : σ.IsIrreducible) {ψ : ℝ → ℂ}
    (hmul : ∀ x y, ψ (x + y) = ψ x * ψ y) (hnorm : ∀ x, ‖ψ x‖ = 1) (hne : ∃ x, ψ x ≠ 1) :
    ∃ l₀, whitSpace σ ψ ≤ Submodule.span ℂ {l₀} := by
  by_cases hzero : ∀ l ∈ whitSpace σ ψ, l = 0
  · refine ⟨0, fun l hl => ?_⟩
    rw [hzero l hl]
    exact Submodule.zero_mem _
  push Not at hzero
  obtain ⟨l₀, hl₀W, hl₀⟩ := hzero

  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : hGL2.SmoothFrechet (πσ σ), l₀ w₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hl₀ (ContinuousLinearMap.ext h)
  set L₀ : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ := toLin l₀ with hL₀
  have hL₀c := isSmoothContinuous_toLin l₀
  have hL₀W := isWhit_of_mem hl₀W
  obtain ⟨w₀', hw₀'⟩ := w₀
  have hd := hL₀c.hasDerivAt_map_expG (norm_πσ_le σ) hw₀' 1 lE
  have e1 : (fun s : ℝ => L₀ (hGL2.smoothMap (πσ σ) hw₀' (1 * hGL2.expG (s • lE)))) =
      fun s => ψ s * L₀ ⟨w₀', hw₀'⟩ := by
    funext s
    rw [one_mul, expG_lE]
    exact hl₀W s ⟨w₀', hw₀'⟩
  rw [e1] at hd
  have hβ : HasDerivAt ψ (L₀ (hGL2.smoothMap (πσ σ) (hGL2.isSmoothVector_derivOp (πσ σ) hw₀' lE) 1) /
      L₀ ⟨w₀', hw₀'⟩) 0 := by
    have := hd.div_const (L₀ ⟨w₀', hw₀'⟩)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    exact (mul_div_cancel_right₀ (ψ s) (show L₀ ⟨w₀', hw₀'⟩ ≠ 0 from hw₀)).symm
  obtain ⟨θ, hθ, hβθ⟩ := deriv_char_eq hmul hnorm hne hβ
  rw [hβθ] at hβ

  obtain ⟨j, v, v', hvs, hv, hv0, hv's, hv'k, hv'0, htrans⟩ := exists_weight_data hσ hθ hβ
  obtain ⟨α, hα⟩ := weightSpace_eq_smul σ hσ hv hv0
    (by simpa using Lop_mem (isSm_Rop hvs) (Rop_mem hvs hv))

  have hinj : ∀ l ∈ whitSpace σ ψ,
      Wt σ (toLin l) v 0 = 0 →
      Wt σ (toLin l) (dπ σ lH v) 0 = 0 → l = 0 := by
    intro l hlW h0 h1
    set L : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ := toLin l with hLdef
    have hLc := isSmoothContinuous_toLin l
    have hLW := isWhit_of_mem hlW
    have hWv := Wt_eq_zero_of_init hLc hβ hLW hvs hv hα h0 h1
    have hWv' := htrans L hLc hLW hWv
    have horb := lT_map_eq_zero hσ hLW hvs hv hv0 hv's hv'k hv'0 hWv hWv'
    have hL0 : L = 0 := hGL2.eq_zero_of_forall_map_eq_zero (πσ σ) (norm_πσ_le σ) hLc hvs
      (topologicalClosure_span_orbit hσ hv0) (fun g => by
        rw [← horb g, lT_of (isSm_map σ hvs g)]; rfl)
    ext w
    exact LinearMap.congr_fun hL0 w

  have hT₀ : Wt σ L₀ v 0 ≠ 0 ∨ Wt σ L₀ (dπ σ lH v) 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hl₀ (hinj l₀ hl₀W h.1 h.2)
  refine ⟨l₀, fun l hlW => ?_⟩
  set Ll : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ := toLin l
  have hLlc := isSmoothContinuous_toLin l
  have hLlW := isWhit_of_mem hlW
  have hwr := Wt_wronskian hL₀c hLlc hθ hβ hL₀W hLlW hvs hv hα
  set a := Wt σ L₀ v 0
  set b := Wt σ L₀ (dπ σ lH v) 0
  set c := Wt σ Ll v 0
  set d := Wt σ Ll (dπ σ lH v) 0

  obtain ⟨r, hrc, hrd⟩ : ∃ r : ℂ, c = r * a ∧ d = r * b := by
    rcases hT₀ with ha | hb
    · refine ⟨c / a, by field_simp, ?_⟩
      field_simp
      linear_combination hwr
    · refine ⟨d / b, ?_, by field_simp⟩
      field_simp
      linear_combination -hwr
  rw [Submodule.mem_span_singleton]
  refine ⟨r, ?_⟩
  have hmem : l - r • l₀ ∈ whitSpace σ ψ :=
    (whitSpace σ ψ).sub_mem hlW ((whitSpace σ ψ).smul_mem r hl₀W)
  have hz := hinj _ hmem (by
      rw [toLin_sub_smul, Wt_sub_smul hvs, ← hrc]; ring) (by
      rw [toLin_sub_smul, Wt_sub_smul (isSm_dπ σ hvs lH), ← hrd]; ring)
  rw [sub_eq_zero] at hz
  exact hz.symm

theorem rank_whitSpace_le_one (hσ : σ.IsIrreducible) {ψ : ℝ → ℂ}
    (hmul : ∀ x y, ψ (x + y) = ψ x * ψ y) (hnorm : ∀ x, ‖ψ x‖ = 1) (hne : ∃ x, ψ x ≠ 1) :
    Module.rank ℂ (whitSpace σ ψ) ≤ 1 := by
  obtain ⟨l₀, hle⟩ := exists_whitSpace_le_span hσ hmul hnorm hne
  refine (Submodule.rank_mono hle).trans ?_
  refine (rank_span_le _).trans ?_
  simp

end GroundTheory.Automorphic.ArchWhittaker
