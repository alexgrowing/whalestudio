import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}

theorem tensor_group_mul_kDiag (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ (g * k) f = tensGrp dual σ g (kDiag dual σ k f) := by
  obtain ⟨hu, hkJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at this
  have hkU : k ∈ UJset ε := by
    show kᴴ * Jm ε * k = Jm ε
    rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hσ' : σ (g * k) = (σ g).comp (σ k) := hσ.1.2 g hg k hkU
  have hkinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  funext c
  simp only [tensGrp, kDiag, hσ', ContinuousLinearMap.comp_apply, map_sum, map_smul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  cases dual
  · simp [Matrix.mul_apply]
  · simp only [cond_true]
    rw [Matrix.mul_inv_rev, hkinv, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun e _ => by rw [Matrix.conjTranspose_apply, mul_comm]

theorem tensor_phi_of_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    oa1Phi dual g c d =
      cond dual ((if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1)) (g c d) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  cases dual
  · rfl
  · have hJJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      split_ifs <;> norm_num
    have hinv : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ])
    simp only [oa1Phi, cond_true]
    rw [hinv]
    simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

theorem norm_tensor_phi_le_sqrt_hs {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (dual : Bool) (c d : Fin n) :
    ‖oa1Phi dual g c d‖ ≤ Real.sqrt (S7.hs g) := by
  have hent : ‖g c d‖ ≤ Real.sqrt (S7.hs g) := by
    have h1 : ‖g c d‖ ^ 2 ≤ ∑ j', ‖g c j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖g c j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)
    have h2 : ∑ j', ‖g c j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ c)
    have h3 : ‖g c d‖ ^ 2 ≤ S7.hs g := by
      simp only [S7.hs, Formalism.REAL.hs]
      exact h1.trans h2
    have h4 := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at h4
  rw [tensor_phi_of_unitary hg dual c d]
  cases dual
  · exact hent
  · have hb : ∀ b : Bool, ‖(if b then (1 : ℂ) else -1)‖ = 1 := by
      intro b
      cases b <;> simp
    simp only [cond_true, norm_mul, norm_star]
    rw [hb, hb, one_mul, mul_one]
    exact hent

theorem smoothOnG_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) : Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, F i x) := by
  unfold Formalism.REAL.SmoothOnG at h ⊢
  intro g₀ hg₀
  choose! U F hU hgU hF hFU using fun i (hi : i ∈ s) => h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, F i x, isOpen_biInter_finset fun i hi => hU i hi,
    Set.mem_iInter₂.2 fun i hi => hgU i hi,
    ContDiffOn.sum fun i hi => (hF i hi).mono (Set.biInter_subset_of_mem hi), fun g hg hgJ => ?_⟩
  exact Finset.sum_congr rfl fun i hi => hFU i hi g (Set.mem_iInter₂.1 hg i hi) hgJ

theorem smoothOnG_inner_rep (w : H) {v : H} (hv : IsSmoothVecU ε σ v) :
    Formalism.REAL.SmoothOnG ε (fun g => inner ℂ w (σ g v)) := by
  unfold IsSmoothVecU S7.SmoothOnGV at hv
  unfold Formalism.REAL.SmoothOnG
  intro g₀ h₀
  obtain ⟨U, F, hU, h0U, hF, hFU⟩ := hv g₀ h₀
  refine ⟨U, fun g => inner ℂ w (F g), hU, h0U, contDiffOn_const.inner ℂ hF, fun g hg hgJ => ?_⟩
  simp only [hFU g hg hgJ]

theorem smoothOnG_tensor_phi (dual : Bool) (c d : Fin n) : Formalism.REAL.SmoothOnG ε (fun g => oa1Phi dual g c d) := by
  have hent : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g c d) := by
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => M c d, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hst : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => star (g c d)) := by
    let L' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun M => star (M c d)
        map_add' := fun _ _ => by simp
        map_smul' := fun r M => by simp [Complex.real_smul, Complex.conj_ofReal] <;> ring }
    exact (LinearMap.toContinuousLinearMap L').contDiff
  unfold Formalism.REAL.SmoothOnG
  intro g₀ _
  cases dual
  · exact ⟨Set.univ, fun g => g c d, isOpen_univ, trivial, hent.contDiffOn, fun g _ _ => rfl⟩
  · refine ⟨Set.univ, fun g => (if ε d then (1 : ℂ) else -1) * star (g c d) * (if ε c then (1 : ℂ) else -1),
      isOpen_univ, trivial, ((contDiff_const.mul hst).mul contDiff_const).contDiffOn, fun g _ hg => ?_⟩
    beta_reduce
    rw [tensor_phi_of_unitary hg true c d]
    rfl

private lemma smoothOnG_mul {f g : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    (hg : Formalism.REAL.SmoothOnG ε g) : Formalism.REAL.SmoothOnG ε (fun x => f x * g x) := by
  unfold Formalism.REAL.SmoothOnG at hf hg ⊢
  intro g₀ h₀
  obtain ⟨U, F, hU, h0U, hF, hFU⟩ := hf g₀ h₀
  obtain ⟨V, G, hV, h0V, hG, hGV⟩ := hg g₀ h₀
  refine ⟨U ∩ V, fun x => F x * G x, hU.inter hV, ⟨h0U, h0V⟩,
    (hF.mono Set.inter_subset_left).mul (hG.mono Set.inter_subset_right), fun x hx hxJ => ?_⟩
  simp only [hFU x hx.1 hxJ, hGV x hx.2 hxJ]

theorem tensor_coef_smooth (dual : Bool) (η f : Fin n → H) (hf : ∀ d, IsSmoothVecU ε σ (f d)) :
    Formalism.REAL.SmoothOnG ε (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) := by
  have heq : (fun g => ∑ c, inner ℂ (η c) (tensGrp dual σ g f c)) =
      fun g => ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
    funext g
    simp only [tensGrp, inner_sum, inner_smul_right, oa1Phi]
  rw [heq]
  exact smoothOnG_finset_sum univ (fun c g => ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d))) fun c _ =>
    smoothOnG_finset_sum univ (fun d g => oa1Phi dual g c d * inner ℂ (η c) (σ g (f d))) fun d _ =>
      smoothOnG_mul (smoothOnG_tensor_phi dual c d) (smoothOnG_inner_rep (η c) (hf d))

theorem continuous_umat' : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_rep_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous continuous_umat' fun g => g.2

theorem continuous_tensor_phi (dual : Bool) (c d : Fin n) :
    Continuous (fun g : Formalism.REAL.UJ ε => oa1Phi dual (Formalism.MainNotions.S.umat g) c d) := by
  have he : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g c d) :=
    (continuous_apply d).comp ((continuous_apply c).comp continuous_umat')
  cases dual
  · exact he
  · have hfun : (fun g : Formalism.REAL.UJ ε => oa1Phi true (Formalism.MainNotions.S.umat g) c d) = fun g =>
        (if ε d then (1 : ℂ) else -1) * star (Formalism.MainNotions.S.umat g c d) * (if ε c then (1 : ℂ) else -1) := by
      funext g
      rw [tensor_phi_of_unitary (g := Formalism.MainNotions.S.umat g) (show inUJ ε (Formalism.MainNotions.S.umat g) from g.2) true c d]
      rfl
    rw [hfun]
    exact (continuous_const.mul he.star).mul continuous_const

theorem tensor_term_memLp (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (dual : Bool) {w v : D} (hw : w ∈ S) (hv : v ∈ S) (c d : Fin n) :
    MemLp (fun g : Formalism.REAL.UJ ε =>
      oa1Phi dual (Formalism.MainNotions.S.umat g) c d * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε) := by
  refine MemLp.of_le (hW v hv w hw) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner (continuous_rep_orbit hσ _))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (norm_tensor_phi_le_sqrt_hs (show inUJ ε (Formalism.MainNotions.S.umat g) from g.2) dual c d) (norm_nonneg _)

theorem tensor_coef_memLp (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {S : Submodule ℂ D}
    (hW : ∀ v ∈ S, ∀ w ∈ S, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (η f : Fin n → D) (hη : η ∈ tensSub S) (hf : f ∈ tensSub S) :
    MemLp (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) 2 (Formalism.REAL.muG ε) := by
  have e : (fun g : Formalism.REAL.UJ ε => ∑ c, inner ℂ ((η c : D) : H)
      (tensGrp dual σ (Formalism.MainNotions.S.umat g) (fun c => ((f c : D) : H)) c)) = fun g =>
      ∑ c, ∑ d, oa1Phi dual (Formalism.MainNotions.S.umat g) c d *
        inner ℂ ((η c : D) : H) (σ (Formalism.MainNotions.S.umat g) ((f d : D) : H)) :=
    funext fun g => tensor_coef_expand dual σ _ _ _
  rw [e]
  rw [tset_mem] at hη hf
  exact memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => tensor_term_memLp hσ hW dual (hη c) (hf d) c d

end ReciprocityTheory.ChartRestriction.DS
