import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec

noncomputable section

namespace RootFieldNumerics

open Filter Topology Matrix

namespace FlImm

variable {N e : ℕ}

def cutRows (A : Matrix (Fin N) (Fin N) ℂ) (b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a c => if a ≤ b then A a c else (1 : Matrix (Fin N) (Fin N) ℂ) a c

def upT (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun c b => ((cutRows A b)⁻¹ *ᵥ Pi.single b 1) c

theorem cutRows_one (b : Fin N) : cutRows (1 : Matrix (Fin N) (Fin N) ℂ) b = 1 := by
  ext a c
  simp [cutRows]

theorem upT_one : upT (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  ext c b
  simp [upT, cutRows_one, Matrix.one_apply, Pi.single_apply]

theorem upT_spec {A : Matrix (Fin N) (Fin N) ℂ} (h : ∀ b, (cutRows A b).det ≠ 0) (a b : Fin N) :
    (b < a → upT A a b = 0) ∧ (a ≤ b → (A * upT A) a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b) := by
  have k : cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (h b)), Matrix.one_mulVec]
  have k1 := congrFun k a
  constructor
  · intro hba
    have e1 : (cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a =
        ((1 : Matrix (Fin N) (Fin N) ℂ) *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a := by
      generalize (cutRows A b)⁻¹ *ᵥ Pi.single b 1 = w
      simp only [Matrix.mulVec, dotProduct, cutRows, Matrix.of_apply, if_neg (not_le.2 hba)]
    rw [e1, Matrix.one_mulVec, Pi.single_eq_of_ne hba.ne'] at k1
    exact k1
  · intro hab
    have e1 : (cutRows A b *ᵥ ((cutRows A b)⁻¹ *ᵥ Pi.single b 1)) a = (A * upT A) a b := by
      simp only [Matrix.mul_apply, upT, Matrix.of_apply]
      generalize (cutRows A b)⁻¹ *ᵥ Pi.single b 1 = w
      simp only [Matrix.mulVec, dotProduct, cutRows, Matrix.of_apply, if_pos hab]
    rw [← e1, k1, Matrix.one_apply, Pi.single_apply]

theorem an_mul {f g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (hg : ∀ a b, AnalyticAt ℂ (fun z => g z a b) t) (a b : Fin N) :
    AnalyticAt ℂ (fun z => (f z * g z) a b) t := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hf a c).mul (hg c b)

theorem an_cut {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (b a c : Fin N) : AnalyticAt ℂ (fun z => cutRows (f z) b a c) t := by
  by_cases h : a ≤ b
  · simpa only [cutRows, Matrix.of_apply, if_pos h] using hf a c
  · simpa only [cutRows, Matrix.of_apply, if_neg h] using analyticAt_const

theorem an_upT {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (h : ∀ b, (cutRows (f t) b).det ≠ 0) (c b : Fin N) :
    AnalyticAt ℂ (fun z => upT (f z) c b) t :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) c).analyticAt _).comp
    (SheetDecomposition.vecInvAn (h := fun z => cutRows (f z) b) (w := fun _ => Pi.single b 1) (an_cut hf b) (h b) analyticAt_const)

def dM (f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (t v : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => fderiv ℂ (fun z => f z a b) t v

theorem dM_mul {f g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ}
    (hf : ∀ a b, AnalyticAt ℂ (fun z => f z a b) t) (hg : ∀ a b, AnalyticAt ℂ (fun z => g z a b) t) (v : Fin e → ℂ) :
    dM (fun z => f z * g z) t v = dM f t v * g t + f t * dM g t v := by
  ext a b
  have h : HasFDerivAt (fun z => ∑ c, f z a c * g z c b)
      (∑ c, (f t a c • fderiv ℂ (fun z => g z c b) t + g t c b • fderiv ℂ (fun z => f z a c) t)) t :=
    HasFDerivAt.fun_sum fun c _ =>
      (hf a c).differentiableAt.hasFDerivAt.fun_mul (hg c b).differentiableAt.hasFDerivAt
  simp only [dM, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  rw [h.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem dM_const (A : Matrix (Fin N) (Fin N) ℂ) (t v : Fin e → ℂ) : dM (fun _ => A) t v = 0 := by
  ext a b
  simp [dM]

theorem dM_zero {f : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {t : Fin e → ℂ} (v : Fin e → ℂ) {a b : Fin N} {c : ℂ}
    (h : ∀ᶠ z in 𝓝 t, f z a b = c) : dM f t v a b = 0 := by
  have k : (fun z => f z a b) =ᶠ[𝓝 t] fun _ => c := h
  simp [dM, k.fderiv_eq]

theorem eq_zero_of_tri {L W : Matrix (Fin N) (Fin N) ℂ} (hd : IsUnit L.det) (hL : ∀ a b, a < b → L a b = 0)
    (hW : W.BlockTriangular id) (h : ∀ a b, a ≤ b → (L * W) a b = 0) : W = 0 := by
  letI := L.invertibleOfIsUnitDet hd
  have hL' : L.BlockTriangular OrderDual.toDual := fun a b hab => hL a b hab
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hL'
  ext a b
  rcases lt_or_ge b a with hab | hab
  · exact hW hab
  · have e1 : W = L⁻¹ * (L * W) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
    rw [e1, Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases le_or_gt c b with hc | hc
    · rw [h c b hc, mul_zero]
    · have hac : a < c := lt_of_le_of_lt hab hc
      rw [hI (OrderDual.toDual_lt_toDual.2 hac), zero_mul]

end FlImm

open FlImm

theorem flagImm_of : RankLem → FlagImm := by
  intro hR Ψ _ N e V gm hV hne han hdet hc
  classical
  obtain ⟨t₀, ht₀⟩ := hne
  let A : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => (gm τ t₀)⁻¹ * gm τ t
  let T : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => upT (A τ t)
  let L : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ t => A τ t * T τ t
  have hA0 : ∀ τ, A τ t₀ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hdet t₀ ht₀ τ)
  have hA : ∀ t ∈ V, ∀ τ a b, AnalyticAt ℂ (fun z => A τ z a b) t := fun t ht τ =>
    an_mul (f := fun _ => (gm τ t₀)⁻¹) (fun _ _ => analyticAt_const) fun a b => han τ a b t ht
  have hc0 : ∀ τ b, (cutRows (A τ t₀) b).det ≠ 0 := fun τ b => by simp [hA0, cutRows_one]
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ V ∧ (∀ τ b, (cutRows (A τ t) b).det ≠ 0) ∧ ∀ τ, (T τ t).det ≠ 0 := by
    refine (hV.eventually_mem ht₀).and (Filter.Eventually.and ?_ ?_)
    · exact Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun b =>
        (SheetDecomposition.vecDetAn (h := fun z => cutRows (A τ z) b) (an_cut (hA t₀ ht₀ τ) b)).continuousAt.eventually_ne (hc0 τ b)
    · refine Filter.eventually_all.2 fun τ => ?_
      refine (SheetDecomposition.vecDetAn (h := T τ) (an_upT (hA t₀ ht₀ τ) (hc0 τ))).continuousAt.eventually_ne ?_
      show (upT (A τ t₀)).det ≠ 0
      simp [hA0, upT_one]
  obtain ⟨W, hW, hWo, hW0⟩ := eventually_nhds_iff.1 hev
  have hT : ∀ t ∈ W, ∀ τ a b, AnalyticAt ℂ (fun z => T τ z a b) t := fun t ht τ =>
    an_upT (hA t (hW t ht).1 τ) ((hW t ht).2.1 τ)
  have hL : ∀ t ∈ W, ∀ τ a b, AnalyticAt ℂ (fun z => L τ z a b) t := fun t ht τ =>
    an_mul (hA t (hW t ht).1 τ) (hT t ht τ)
  have hTt : ∀ t ∈ W, ∀ τ, (T τ t).BlockTriangular id := fun t ht τ a b hab =>
    (upT_spec ((hW t ht).2.1 τ) a b).1 hab
  have hLs : ∀ t ∈ W, ∀ τ a b, a ≤ b → L τ t a b = (1 : Matrix (Fin N) (Fin N) ℂ) a b := fun t ht τ a b hab =>
    (upT_spec ((hW t ht).2.1 τ) a b).2 hab
  have hgL : ∀ τ t, gm τ t₀ * L τ t = gm τ t * T τ t := fun τ t => by
    simp only [L, A, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet t₀ ht₀ τ), Matrix.one_mul]
  let q := (Fintype.equivFin (Ψ × Fin N × Fin N)).symm
  let Φ : (Fin e → ℂ) → Fin (Fintype.card (Ψ × Fin N × Fin N)) → ℂ := fun t i => L (q i).1 t (q i).2.1 (q i).2.2
  obtain ⟨t, ht, hinj⟩ := hR e _ W Φ hWo ⟨t₀, hW0⟩ (fun t ht => analyticAt_pi_iff.2 fun i => hL t ht _ _ _) (by
    intro t ht
    refine (hc t (hW t ht).1).mono fun t' ht' => ?_
    refine And.intro (hW t' ht'.1).1 fun τ => ?_
    have e1 : L τ t' = L τ t := by
      ext a b
      simpa [Φ] using congrFun ht'.2 (q.symm (τ, a, b))
    have hu : IsUnit (T τ t').det := IsUnit.mk0 _ ((hW t' ht'.1).2.2 τ)
    letI := (T τ t').invertibleOfIsUnitDet hu
    refine ⟨T τ t * (T τ t')⁻¹, (hTt t ht τ).mul (Matrix.blockTriangular_inv_of_blockTriangular (hTt t' ht'.1 τ)), ?_⟩
    show gm τ t' = gm τ t * (T τ t * (T τ t')⁻¹)
    rw [← Matrix.mul_assoc, ← hgL, ← e1, hgL, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one])
  refine ⟨t, (hW t ht).1, fun v hv => ?_⟩
  have hWn : ∀ᶠ z in 𝓝 t, z ∈ W := hWo.eventually_mem ht
  have hdL : ∀ τ, dM (L τ) t v = 0 := fun τ => by
    have hu : IsUnit (T τ t).det := IsUnit.mk0 _ ((hW t ht).2.2 τ)
    have hg := hdet t (hW t ht).1 τ
    have hg0 := hdet t₀ ht₀ τ
    letI := (T τ t).invertibleOfIsUnitDet hu
    have e1 : dM (fun z => gm τ t₀ * L τ z) t v = dM (fun z => gm τ z * T τ z) t v := by simp only [hgL]
    rw [dM_mul (f := fun _ => gm τ t₀) (fun _ _ => analyticAt_const) (hL t ht τ), dM_const, Matrix.zero_mul, zero_add,
      dM_mul (fun a b => han τ a b t (hW t ht).1) (hT t ht τ)] at e1
    let X := (T τ t)⁻¹ * (((gm τ t)⁻¹ * dM (gm τ) t v) * T τ t + dM (T τ) t v)
    have hX : X.BlockTriangular id := by
      refine (Matrix.blockTriangular_inv_of_blockTriangular (hTt t ht τ)).mul (((hv τ).mul (hTt t ht τ)).add ?_)
      intro a b hab
      exact dM_zero v (hWn.mono fun z hz => hTt z hz τ hab)
    have e2 : L τ t * X = dM (L τ) t v := by
      have e3 : gm τ t₀ * (L τ t * X) = gm τ t₀ * dM (L τ) t v := by
        rw [e1, ← Matrix.mul_assoc, hgL]
        simp only [X, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_add,
          Matrix.mul_nonsing_inv_cancel_left _ _ hg]
      have e4 := congrArg (fun Z => (gm τ t₀)⁻¹ * Z) e3
      simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hg0] using e4
    have hLu : IsUnit (L τ t).det := by
      have e5 : (gm τ t₀).det * (L τ t).det = (gm τ t).det * (T τ t).det := by
        rw [← Matrix.det_mul (gm τ t₀), hgL, Matrix.det_mul]
      have e6 := hg.mul hu
      rw [← e5] at e6
      exact isUnit_of_mul_isUnit_right e6
    have hX0 : X = 0 := eq_zero_of_tri hLu (fun a b hab => by rw [hLs t ht τ a b hab.le, Matrix.one_apply_ne hab.ne]) hX
      fun a b hab => by
        rw [e2]
        exact dM_zero v (hWn.mono fun z hz => hLs z hz τ a b hab)
    rw [← e2, hX0, Matrix.mul_zero]
  refine hinj (?_ : fderiv ℂ Φ t v = fderiv ℂ Φ t 0)
  rw [map_zero]
  ext i
  have k := fderiv_pi (𝕜 := ℂ) (φ := fun i z => L (q i).1 z (q i).2.1 (q i).2.2) (x := t)
    fun i => (hL t ht _ _ _).differentiableAt
  show fderiv ℂ (fun z i => L (q i).1 z (q i).2.1 (q i).2.2) t v i = 0
  rw [k]
  exact congrFun (congrFun (hdL (q i).1) (q i).2.1) (q i).2.2

end RootFieldNumerics
