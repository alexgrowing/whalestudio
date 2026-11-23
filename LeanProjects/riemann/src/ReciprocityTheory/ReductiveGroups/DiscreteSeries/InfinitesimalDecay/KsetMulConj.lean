import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothCore

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_smooth (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (dS σ X v) :=
  IsSmoothVecU.dS hσ hX hv

theorem dSW_cons (X : Matrix (Fin n) (Fin n) ℂ) (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ (X :: w) v = dS σ X (dSW σ w v) := rfl

theorem dSW_append (a b : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ (a ++ b) v = dSW σ a (dSW σ b v) := by
  induction a with
  | nil => rfl
  | cons X a ih => rw [List.cons_append, dSW_cons, dSW_cons, ih]

theorem dSW_smooth (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v : H} (hv : IsSmoothVecU ε σ v) : IsSmoothVecU ε σ (dSW σ w v) := by
  induction w with
  | nil => exact hv
  | cons X w ih =>
    rw [dSW_cons]
    exact IsSmoothVecU.dS hσ (hw X (by simp)) (ih (fun Y hY => hw Y (by simp [hY])))

theorem dSW_add (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v v' : H} (hv : IsSmoothVecU ε σ v) (hv' : IsSmoothVecU ε σ v') :
    dSW σ w (v + v') = dSW σ w v + dSW σ w v' := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    rw [dSW_cons, dSW_cons, dSW_cons, ih hw',
      dS_add_vec hσ (hw X (by simp)) (dSW_smooth hσ hw' hv) (dSW_smooth hσ hw' hv')]

theorem dSW_smul (c : ℂ) (w : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) :
    dSW σ w (c • v) = c • dSW σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih => rw [dSW_cons, dSW_cons, ih, dS_smul_vec]

theorem dSW_sub (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {v v' : H} (hv : IsSmoothVecU ε σ v) (hv' : IsSmoothVecU ε σ v') :
    dSW σ w (v - v') = dSW σ w v - dSW σ w v' := by
  have e : v - v' = v + (-1 : ℂ) • v' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, dSW_add hσ hw hv (IsSmoothVecU.smul (-1) hv'), dSW_smul, neg_one_smul, sub_eq_add_neg]

private lemma exp_real_smul_mem_UJset_of_inG {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
  have h : inG ε ((t : ℂ) • X) := by
    unfold inG at hX ⊢
    have e : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
      rw [Matrix.conjTranspose_smul]
      congr 1
      exact Complex.conj_ofReal t
    rw [e, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
  exact Formalism.REAL.f1alg_exp_inUJ ε _ h

private lemma inner_map_map_of_isURepOn (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (y v : H) : inner ℂ (σ g y) (σ g v) = inner ℂ y v := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map y v

theorem inner_dS_add (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {y v : H}
    (hy : IsSmoothVecU ε σ y) (hv : IsSmoothVecU ε σ v) :
    inner ℂ (dS σ X y) v + inner ℂ y (dS σ X v) = 0 := by
  have hf : HasDerivAt
      (fun t : ℝ => inner ℂ (σ (NormedSpace.exp ((t : ℂ) • X)) y) (σ (NormedSpace.exp ((t : ℂ) • X)) v))
      (inner ℂ (σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) y) (dS σ X v) +
        inner ℂ (dS σ X y) (σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) v)) 0 :=
    (hasDerivAt_dS hσ hX hy).inner ℂ (hasDerivAt_dS hσ hX hv)
  have hc : (fun t : ℝ => inner ℂ (σ (NormedSpace.exp ((t : ℂ) • X)) y)
      (σ (NormedSpace.exp ((t : ℂ) • X)) v)) = fun _ => inner ℂ y v := by
    funext t
    exact inner_map_map_of_isURepOn hσ (exp_real_smul_mem_UJset_of_inG hX t) y v
  rw [hc] at hf
  have h0 : σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    exact hσ.1.1
  rw [h0] at hf
  have h2 := hf.unique (hasDerivAt_const (0 : ℝ) (inner ℂ y v))
  simpa [add_comm] using h2

theorem inner_dSW (hσ : IsURepOn (UJset ε) σ) {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X)
    {y v : H} (hy : IsSmoothVecU ε σ y) (hv : IsSmoothVecU ε σ v) :
    inner ℂ y (dSW σ w v) = (-1 : ℂ) ^ w.length * inner ℂ (dSW σ w.reverse y) v := by
  induction w generalizing y with
  | nil =>
    simp only [List.reverse_nil, List.length_nil, pow_zero, one_mul]
    rfl
  | cons X w ih =>
    have hX : inG ε X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    have hXy : IsSmoothVecU ε σ (dS σ X y) := IsSmoothVecU.dS hσ hX hy
    have h1 := inner_dS_add hσ hX hy (dSW_smooth hσ hw' hv)
    have h2 : inner ℂ (dS σ X y) (dSW σ w v) =
        (-1 : ℂ) ^ w.length * inner ℂ (dSW σ w.reverse (dS σ X y)) v := ih (y := dS σ X y) hw' hXy
    have e : dSW σ [X] y = dS σ X y := rfl
    rw [dSW_cons, eq_neg_of_add_eq_zero_right h1, h2, List.reverse_cons, dSW_append, e,
      List.length_cons, pow_succ]
    ring

theorem inG_conj_K {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) : inG ε (kᴴ * X * k) := by
  have hu : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  have hu' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hc : k * Jm ε = Jm ε * k := hk.2
  have hc' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * (Jm ε * k) * kᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]
      _ = kᴴ * (k * Jm ε) * kᴴ := by rw [hc]
      _ = Jm ε * kᴴ := by rw [← Matrix.mul_assoc, hu', Matrix.one_mul]
  unfold inG at hX ⊢
  have e : (kᴴ * X * k)ᴴ * Jm ε + Jm ε * (kᴴ * X * k) = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_add, Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc, hc]
    · simp only [← Matrix.mul_assoc, hc']
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem Kset_mul_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k * kᴴ = 1 ∧ kᴴ * k = 1 := by
  exact ⟨Matrix.mem_unitaryGroup_iff.mp hk.1, Matrix.mem_unitaryGroup_iff'.mp hk.1⟩

theorem dS_conj (hσ : IsURepOn (UJset ε) σ) {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X)
    {v : H} (hv : IsSmoothVecU ε σ v) : dS σ X (σ k v) = σ k (dS σ (kᴴ * X * k) v) := by
  obtain ⟨hu, hu'⟩ := Kset_mul_conj hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu'
  have hunit : IsUnit k := (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse hu')
  have hkU : k ∈ UJset ε := by
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu', Matrix.one_mul]
  have hY : inG ε (kᴴ * X * k) := inG_conj_K hk hX
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ k v)) =
      fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • (kᴴ * X * k))) v) := by
    funext t
    have he : NormedSpace.exp ((t : ℂ) • X) * k = k * NormedSpace.exp ((t : ℂ) • (kᴴ * X * k)) := by
      have h1 : (t : ℂ) • (kᴴ * X * k) = k⁻¹ * ((t : ℂ) • X) * k := by
        rw [hinv, Matrix.mul_smul, Matrix.smul_mul]
      rw [h1, Matrix.exp_conj' k _ hunit, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu,
        Matrix.one_mul]
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (exp_real_smul_mem_UJset_of_inG hX t) _ hkU, he,
      hσ.1.2 _ hkU _ (exp_real_smul_mem_UJset_of_inG hY t), ContinuousLinearMap.comp_apply]
  have hd := hasDerivAt_dS hσ hY hv
  have hd2 : HasDerivAt (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • (kᴴ * X * k))) v))
      (σ k (dS σ (kᴴ * X * k) v)) 0 :=
    ((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  rw [show dS σ X (σ k v) = deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ k v)) 0 from rfl,
    hfun]
  exact hd2.deriv

theorem dSW_conj (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X) {v : H} (hv : IsSmoothVecU ε σ v) :
    dSW σ w (σ k v) = σ k (dSW σ (w.map fun X => kᴴ * X * k) v) := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    have hX : inG ε X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inG ε Y := fun Y hY => hw Y (by simp [hY])
    have hm : ∀ Y ∈ w.map (fun X => kᴴ * X * k), inG ε Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inG_conj_K hk (hw' Z hZ)
    rw [List.map_cons, dSW_cons, dSW_cons, ih hw', dS_conj hσ hk hX (dSW_smooth hσ hm hv)]

end ReciprocityTheory.ChartRestriction.DS.DecInf
