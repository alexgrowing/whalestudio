import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

private lemma exp_smul_mem_Kset_of_skew_of_commute_Jm (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Jm ε = Jm ε * X) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  have hs : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hX, smul_neg]
    first
    | simp
    | (congr 2; exact Complex.conj_ofReal t)
  show NormedSpace.exp ((t : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X)
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs]
    have hc : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := Commute.neg_left (Commute.refl _)
    have he : NormedSpace.exp (-((t : ℂ) • X) + (t : ℂ) • X) =
        NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X) := by
      first
      | exact Matrix.exp_add_of_commute _ _ hc
      | exact Matrix.exp_add_of_commute hc
      | exact NormedSpace.exp_add_of_commute hc
    rw [← he, neg_add_cancel]
    first
    | exact NormedSpace.exp_zero
    | simp
  · first
    | exact ((show Commute X (Jm ε) from hJ).smul_left (t : ℂ)).exp_left
    | exact Commute.exp_left ((show Commute X (Jm ε) from hJ).smul_left (t : ℂ))

private lemma mem_UJset_of_mem_Kset' {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg' : g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g := hg
  obtain ⟨hu, hc⟩ := hg'
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp hu, Matrix.one_mul]

private lemma inG_of_skewHermitian_of_commute_Jm (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Jm ε = Jm ε * X) : inG ε X := by
  show Xᴴ * Jm ε + Jm ε * X = 0
  rw [hX, neg_mul, hJ, neg_add_cancel]

private lemma deriv_mem_submodule_of_forall_mem {S : Submodule ℂ H} [FiniteDimensional ℂ S] {f : ℝ → H} {f' : H}
    (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have hcl : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  refine hcl.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hf)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact (S.restrictScalars ℝ).smul_mem _ (S.sub_mem (hS t) (hS 0))

private lemma exp_smul_diagonal_I (φ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal (fun b => (φ b : ℂ) * Complex.I)) =
      Matrix.diagonal (fun b => Complex.exp (((t * φ b : ℝ) : ℂ) * Complex.I)) := by
  have h : (t : ℂ) • Matrix.diagonal (fun b => (φ b : ℂ) * Complex.I) =
      Matrix.diagonal (fun b => ((t * φ b : ℝ) : ℂ) * Complex.I) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      push_cast
      ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [h, Matrix.exp_diagonal]
  congr 1
  funext b
  first
  | (rw [Pi.exp_apply, ← Complex.exp_eq_exp_ℂ])
  | (simp only [Pi.exp_apply]; exact (congrFun Complex.exp_eq_exp_ℂ _).symm)
  | simp [Complex.exp_eq_exp_ℂ]

private lemma diagonal_I_conjTranspose_eq_neg (φ : Fin n → ℝ) :
    (Matrix.diagonal (fun b => (φ b : ℂ) * Complex.I))ᴴ =
      -Matrix.diagonal (fun b => (φ b : ℂ) * Complex.I) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    first
    | simp [Matrix.conjTranspose_apply]
    | simp [Matrix.conjTranspose_apply, Complex.star_def]
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

private lemma diagonal_commute_Jm (d : Fin n → ℂ) :
    Matrix.diagonal d * Jm ε = Jm ε * Matrix.diagonal d := by
  simp only [Jm, Matrix.diagonal_mul_diagonal]
  congr 1
  funext b
  ring

private lemma actM_diagonal {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E' : Fin n → Fin n → Module.End ℂ M) (d : Fin n → ℂ) (x : M) :
    actM E' (Matrix.diagonal d) x = ∑ a, d a • E' a a x := by
  simp [actM, Matrix.diagonal_apply, ite_smul]

private lemma eq_exp_smul_of_hasDerivAt_smul_self {f : ℝ → H} {c : ℂ} (hf : ∀ t, HasDerivAt f (c • f t) t) (t : ℝ) :
    f t = Complex.exp ((t : ℂ) * c) • f 0 := by
  have hg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * -c) • f s) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * -c) (-c) s := by
      have := ((hasDerivAt_id s).ofReal_comp).mul_const (-c)
      exact this.congr_deriv (by simp)
    have h2 := h1.cexp.smul (hf s)
    refine h2.congr_deriv ?_
    rw [smul_smul, ← add_smul, ← mul_add, add_neg_cancel, mul_zero, zero_smul]
  have hc : Complex.exp ((t : ℂ) * -c) • f t = Complex.exp (((0 : ℝ) : ℂ) * -c) • f 0 :=
    is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  calc f t = Complex.exp ((t : ℂ) * c) • (Complex.exp ((t : ℂ) * -c) • f t) := by
        rw [smul_smul, ← Complex.exp_add, mul_neg, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp ((t : ℂ) * c) • f 0 := by
        rw [hc]
        simp

private lemma sigma_exp_smul_eq_exp_smul_of_actM_eigen (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (hJ : X * Jm ε = Jm ε * X) (c : ℂ) (w : D)
    (hw : actM E X w = c • w) (t : ℝ) :
    σ (NormedSpace.exp ((t : ℂ) • X)) (w : H) = Complex.exp ((t : ℂ) * c) • (w : H) := by
  have hU : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • X) ∈ UJset ε :=
    fun s => mem_UJset_of_mem_Kset' (exp_smul_mem_Kset_of_skew_of_commute_Jm X hX hJ s)
  have hd := hD.deriv X (inG_of_skewHermitian_of_commute_Jm X hX hJ) w
  rw [hw, Submodule.coe_smul] at hd
  have hf : ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))
      (c • σ (NormedSpace.exp ((t : ℂ) • X)) (w : H)) t := by
    intro t
    have hL : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H)))
        (σ (NormedSpace.exp ((t : ℂ) • X)) (c • (w : H))) 0 := by
      first
      | exact ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) hd
      | simpa using ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) hd
    have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H)))
        (σ (NormedSpace.exp ((t : ℂ) • X)) (c • (w : H))) (t - t) := by
      rw [sub_self]
      exact hL
    have hL2 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (w : H)))
        (σ (NormedSpace.exp ((t : ℂ) • X)) (c • (w : H))) t := by
      first
      | exact h0.comp_sub_const t t
      | exact HasDerivAt.comp_sub_const t t h0
      | exact h0.comp_sub_const
    have heq : (fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (w : H))) =
        fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (w : H) := by
      funext s
      rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (hU t) _ (hU (s - t))]
      have hc : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
        ((Commute.refl X).smul_left (t : ℂ)).smul_right ((s - t : ℝ) : ℂ)
      have he : NormedSpace.exp ((t : ℂ) • X + ((s - t : ℝ) : ℂ) • X) =
          NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X) := by
        first
        | exact Matrix.exp_add_of_commute _ _ hc
        | exact Matrix.exp_add_of_commute hc
        | exact NormedSpace.exp_add_of_commute hc
      rw [← he, ← add_smul, show (t : ℂ) + ((s - t : ℝ) : ℂ) = (s : ℂ) by push_cast; ring]
    rw [heq, map_smul] at hL2
    exact hL2
  refine (eq_exp_smul_of_hasDerivAt_smul_self hf t).trans ?_
  simp [hσ.1.1]

private lemma actM_diagonal_I_single {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E' : Fin n → Fin n → Module.End ℂ M) (a : Fin n) (x : M) :
    actM E' (Matrix.diagonal (fun b => (((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I)) x =
      Complex.I • E' a a x := by
  rw [actM_diagonal, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

private lemma antisymmetric_unit_conjTranspose_eq_neg (a b : Fin n) :
    (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then (1 : ℂ) else 0) -
      (if j = a ∧ i = b then 1 else 0))ᴴ =
    -(Matrix.of fun i j : Fin n => (if j = b ∧ i = a then (1 : ℂ) else 0) -
      (if j = a ∧ i = b then 1 else 0)) := by
  ext i j
  have e1 : (i = b ∧ j = a) ↔ (j = a ∧ i = b) := and_comm
  have e2 : (i = a ∧ j = b) ↔ (j = b ∧ i = a) := and_comm
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply, e1, e2]
  split_ifs
  all_goals first
    | simp
    | simp [Complex.star_def]
    | (simp; exact Complex.conj_I)

private lemma antisymmetric_unit_commute_Jm_of_same_sign {a b : Fin n} (hab : ε a = ε b) :
    (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then (1 : ℂ) else 0) -
      (if j = a ∧ i = b then 1 else 0)) * Jm ε =
    Jm ε * (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then (1 : ℂ) else 0) -
      (if j = a ∧ i = b then 1 else 0)) := by
  have hd : ∀ i j : Fin n, ((j = b ∧ i = a) ∨ (j = a ∧ i = b)) →
      (if ε i then (1 : ℂ) else -1) = (if ε j then 1 else -1) := by
    rintro i j (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h1, h2, hab]
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hP : j = b ∧ i = a
  · rw [hd i j (Or.inl hP)]
    ring
  · by_cases hQ : j = a ∧ i = b
    · rw [hd i j (Or.inr hQ)]
      ring
    · simp [hP, hQ]

private lemma symmetric_I_unit_conjTranspose_eq_neg (a b : Fin n) :
    (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0))ᴴ =
    -(Matrix.of fun i j : Fin n => (if j = b ∧ i = a then Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0)) := by
  ext i j
  have e1 : (i = b ∧ j = a) ↔ (j = a ∧ i = b) := and_comm
  have e2 : (i = a ∧ j = b) ↔ (j = b ∧ i = a) := and_comm
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply, e1, e2]
  split_ifs
  all_goals first
    | simp
    | simp [Complex.star_def]
    | (simp; exact Complex.conj_I)

private lemma symmetric_I_unit_commute_Jm_of_same_sign {a b : Fin n} (hab : ε a = ε b) :
    (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0)) * Jm ε =
    Jm ε * (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0)) := by
  have hd : ∀ i j : Fin n, ((j = b ∧ i = a) ∨ (j = a ∧ i = b)) →
      (if ε i then (1 : ℂ) else -1) = (if ε j then 1 else -1) := by
    rintro i j (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h1, h2, hab]
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hP : j = b ∧ i = a
  · rw [hd i j (Or.inl hP)]
    ring
  · by_cases hQ : j = a ∧ i = b
    · rw [hd i j (Or.inr hQ)]
      ring
    · simp [hP, hQ]

private lemma actM_antisymmetric_unit {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E' : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (x : M) :
    actM E' (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then (1 : ℂ) else 0) -
      (if j = a ∧ i = b then 1 else 0)) x = E' a b x - E' b a x := by
  simp [actM, sub_smul, Finset.sum_sub_distrib, ite_and, ite_smul]

private lemma actM_symmetric_I_unit {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E' : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (x : M) :
    actM E' (Matrix.of fun i j : Fin n => (if j = b ∧ i = a then Complex.I else 0) +
      (if j = a ∧ i = b then Complex.I else 0)) x =
      Complex.I • E' a b x + Complex.I • E' b a x := by
  simp [actM, add_smul, Finset.sum_add_distrib, ite_and, ite_smul]

theorem isKTypeOf_of_isKIrrHW (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {Λ : Fin n → ℝ}
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E Λ V)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hwt : ∀ (μ : Fin n → ℝ) (x : D), x ∈ V → x ≠ 0 → (∀ a, E a a x = ((μ a : ℝ) : ℂ) • x) →
      Formalism.MainNotions.S.CDom ε μ Λ) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (V.map D.subtype) := by
  unfold Formalism.MainNotions.S.IsKTypeOf
  have hW : FiniteDimensional ℂ (V.map D.subtype) := by
    haveI := hV.1
    first
    | exact Module.Finite.map V D.subtype
    | exact Module.Finite.map _ _
  refine ⟨hW, ?_, ?_, ?_, ?_⟩
  · intro g hg v hv
    obtain ⟨x, hxV, hxv⟩ := Submodule.mem_map.mp hv
    obtain ⟨y, hyV, hy⟩ := hVK g hg x hxV
    rw [← hxv, Submodule.subtype_apply, ← hy]
    exact Submodule.mem_map_of_mem hyV
  · intro S' hle hS'
    haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
    have hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X →
        ∀ v : D, (v : H) ∈ S' → ((actM E X v : D) : H) ∈ S' := by
      intro X hX hJ v hv
      exact deriv_mem_submodule_of_forall_mem (hD.deriv X (inG_of_skewHermitian_of_commute_Jm X hX hJ) v)
        (fun t => hS' _ (exp_smul_mem_Kset_of_skew_of_commute_Jm X hX hJ t) _ hv)
    have hTs : IsKStableSub ε E (V ⊓ S'.comap D.subtype) := by
      intro a b hab v hv
      have hv' := Submodule.mem_inf.mp hv
      have hv2 : (v : H) ∈ S' := Submodule.mem_comap.mp hv'.2
      refine Submodule.mem_inf.mpr ⟨hV.2.1 a b hab v hv'.1, ?_⟩
      have h1 := hmem _ (antisymmetric_unit_conjTranspose_eq_neg a b) (antisymmetric_unit_commute_Jm_of_same_sign hab) v hv2
      have h2 := hmem _ (symmetric_I_unit_conjTranspose_eq_neg a b) (symmetric_I_unit_commute_Jm_of_same_sign hab) v hv2
      rw [actM_antisymmetric_unit] at h1
      rw [actM_symmetric_I_unit] at h2
      have key : (2 : ℂ) • E a b v = (E a b v - E b a v) +
          (-Complex.I) • (Complex.I • E a b v + Complex.I • E b a v) := by
        rw [smul_add (-Complex.I), smul_smul, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
          one_smul, one_smul, two_smul]
        abel
      have h3 : (((2 : ℂ) • E a b v : D) : H) ∈ S' := by
        rw [key, Submodule.coe_add, Submodule.coe_smul]
        exact S'.add_mem h1 (S'.smul_mem _ h2)
      rw [Submodule.coe_smul] at h3
      refine Submodule.mem_comap.mpr ?_
      first
      | exact (S'.smul_mem_iff two_ne_zero).mp h3
      | exact (Submodule.smul_mem_iff _ two_ne_zero).mp h3
    rcases hV.2.2.1 (V ⊓ S'.comap D.subtype) inf_le_left hTs with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨x, hxV, hxy⟩ := Submodule.mem_map.mp (hle hy)
      have hx : x ∈ V ⊓ S'.comap D.subtype :=
        Submodule.mem_inf.mpr ⟨hxV, Submodule.mem_comap.mpr (by rw [hxy]; exact hy)⟩
      rw [h, Submodule.mem_bot] at hx
      rw [← hxy, hx, map_zero]
    · right
      apply le_antisymm hle
      intro y hy
      obtain ⟨x, hxV, hxy⟩ := Submodule.mem_map.mp hy
      rw [← h] at hxV
      rw [← hxy]
      exact Submodule.mem_comap.mp (Submodule.mem_inf.mp hxV).2
  · obtain ⟨w, hwV, hw0, hwHW⟩ := hV.2.2.2
    refine ⟨(w : H), Submodule.mem_map_of_mem hwV, fun h => hw0 (Submodule.coe_eq_zero.mp h), ?_⟩
    intro θ hθ
    have hact : actM E (Matrix.diagonal (fun b => (θ b : ℂ) * Complex.I)) w =
        (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • w := by
      rw [actM_diagonal]
      simp only [hwHW.1, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h := sigma_exp_smul_eq_exp_smul_of_actM_eigen hσ hD (Matrix.diagonal (fun b => (θ b : ℂ) * Complex.I)) (diagonal_I_conjTranspose_eq_neg θ)
      (diagonal_commute_Jm _) (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) w hact 1
    rw [exp_smul_diagonal_I] at h
    simpa using h
  · intro μ v hv hv0 hwt'
    obtain ⟨x, hxV, hxv⟩ := Submodule.mem_map.mp hv
    rw [Submodule.subtype_apply] at hxv
    subst hxv
    refine hwt μ x hxV (fun h => hv0 (by rw [h]; rfl)) (fun a => ?_)
    have hX := diagonal_I_conjTranspose_eq_neg (Pi.single a (1 : ℝ))
    have hJ := diagonal_commute_Jm (ε := ε) (fun b => (((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I)
    have h1 := hD.deriv _ (inG_of_skewHermitian_of_commute_Jm _ hX hJ) x
    have hfeq : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) •
        Matrix.diagonal (fun b => (((Pi.single a (1 : ℝ) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I))) (x : H)) =
        fun s : ℝ => Complex.exp (((μ a * s : ℝ) : ℂ) * Complex.I) • (x : H) := by
      funext s
      have hK := exp_smul_mem_Kset_of_skew_of_commute_Jm _ hX hJ s
      rw [exp_smul_diagonal_I (Pi.single a (1 : ℝ)) s] at hK ⊢
      rw [hwt' _ hK]
      simp [Pi.single_apply]
    rw [hfeq] at h1
    have h3 : HasDerivAt (fun s : ℝ => (((μ a * s : ℝ) : ℂ) * Complex.I))
        ((μ a : ℂ) * Complex.I) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp).mul_const Complex.I
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (((μ a * s : ℝ) : ℂ) * Complex.I) • (x : H))
        (((μ a : ℂ) * Complex.I) • (x : H)) 0 := by
      have := h3.cexp.smul_const (x : H)
      simpa using this
    have h4 := h1.unique h2
    rw [actM_diagonal_I_single, Submodule.coe_smul] at h4
    apply Subtype.ext
    rw [Submodule.coe_smul]
    apply smul_right_injective H Complex.I_ne_zero
    simp only [smul_smul]
    rw [h4, mul_comm]

end ReciprocityTheory.ChartRestriction.DS
