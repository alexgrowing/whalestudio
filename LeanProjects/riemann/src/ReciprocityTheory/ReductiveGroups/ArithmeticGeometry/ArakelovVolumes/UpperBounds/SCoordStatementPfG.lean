import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoF

open MvPolynomial Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
theorem part1 {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    {Fr : Type} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N D : ℕ} (hD : n = D) (sg : K →+* ℂ)
    {dom Gen : Set Fr} (hdom : IsOpen dom) (hGs : Gen ⊆ dom) (hGd : dom ⊆ closure Gen)
    (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (htr : Algebra.trdeg K Ω = D)
    (W : Fin (N + 1) → Fr → ℂ) (hW : ∀ j, DifferentiableOn ℂ (W j) dom)
    (u : Fin (N + 1) → Ω) (j0 : Fin (N + 1)) (hWu : ∀ y ∈ Gen, ∀ j, W j y = pt y (u j) * W j0 y)
    (c : EuclideanSpace ℂ (Fin n) → Fr) (hc : Differentiable ℂ c) {x : Fr} (hc0 : c 0 = x)
    (hx : x ∈ Gen) (hx0 : W j0 x ≠ 0) (jj : Fin n → Fin (N + 1))
    (hJ : (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) 0).det ≠ 0)
    (t : Fin (D + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) * W j x = 0) :
    ∃ Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ),
      (∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0) ∧
      ∃ (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)), M.det ≠ 0 ∧
      (∀ ξ, (∀ k, w k ξ = 0) → ξ = 0) ∧ ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) • Dv j =
        ∑ k, M i k • w k := by
  subst hD
  simp only [Fin.cast_eq_self] at hs ⊢
  set U : Set Fr := dom ∩ W j0 ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := (hW j0).continuousOn.isOpen_inter_preimage hdom isOpen_compl_singleton
  have hUG : U ⊆ closure Gen := fun y hy => hGd hy.1
  have hxU : x ∈ Gen ∩ U := ⟨hx, hGs hx, hx0⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (N + 1) → Fr → ℂ, v = fun j y => W j y / W j0 y := ⟨_, rfl⟩
  have hvd : ∀ j, ∀ y ∈ U, DifferentiableAt ℂ (v j) y := fun j y hy => by
    have h : DifferentiableAt ℂ (fun y => W j y * (W j0 y)⁻¹) y :=
      ((hW j).differentiableAt (hdom.mem_nhds hy.1)).mul
        (((hW j0).differentiableAt (hdom.mem_nhds hy.1)).inv hy.2)
    have hv' : v j = fun y => W j y * (W j0 y)⁻¹ := by rw [hv]; exact funext fun y => div_eq_mul_inv _ _
    rw [hv']; exact h
  have hvG : ∀ y ∈ Gen ∩ U, ∀ j, v j y = pt y (u j) := fun y hy j => by
    rw [hv]; show W j y / W j0 y = _
    rw [hWu y hy.1 j, mul_div_cancel_right₀ _ hy.2.2]
  have hu0 : u j0 = 1 := by
    have h := hvG x hxU j0
    rw [hv] at h
    change W j0 x / W j0 x = _ at h
    rw [div_self hx0] at h
    exact (pt x).injective (by rw [map_one]; exact h.symm)

  let u' : {j : Fin (N + 1) // j ≠ j0} → Ω := fun j => u j.1
  obtain ⟨B, hB⟩ := ((AlgebraicIndependent.matroid K Ω).comap u').exists_isBasis Set.univ
    (by rw [Matroid.comap_ground_eq, AlgebraicIndependent.matroid_e, Set.preimage_univ])
  rw [Matroid.comap_isBasis_iff] at hB
  obtain ⟨hB1, hBinj, -⟩ := hB
  haveI : Fintype B := Fintype.ofFinite B
  let yB : B → Ω := fun b => u b.1.1
  have hyB : AlgebraicIndependent K yB := by
    have h1 := AlgebraicIndependent.matroid_indep_iff.mp hB1.indep
    have h2 := h1.comp (Equiv.Set.imageOfInjOn u' B hBinj) (Equiv.injective _)
    convert h2 using 1
    funext b; rfl
  have hrange : Set.range yB = u' '' B := by
    ext w; simp [yB, u']
  have halg : ∀ j : {j : Fin (N + 1) // j ≠ j0}, IsAlgebraic (Algebra.adjoin K (Set.range yB)) (u j.1) := by
    intro j
    have h1 := hB1.subset_closure (Set.mem_image_of_mem u' (Set.mem_univ j))
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe, Subalgebra.mem_algebraicClosure] at h1
    rwa [hrange]

  have hrel : ∀ j : {j : Fin (N + 1) // j ≠ j0}, ∃ co : B → Ω, fderiv ℂ (fun z => v j.1 (c z)) 0 =
      ∑ b, pt x (co b) • fderiv ℂ (fun z => v b.1.1 (c z)) 0 := fun j =>
    SCoD.rel_deriv sg hU hUG pt hpt (fun b => v b.1.1) (v j.1) (fun b => hvd b.1.1) (hvd j.1) yB (u j.1)
      (fun y hy b => hvG y hy b.1.1) (fun y hy => hvG y hy j.1) hyB (halg j) c hc x hc0 hxU
  choose co hco using hrel
  let a : {j : Fin (N + 1) // j ≠ j0} → B → Ω := fun j => by
    classical exact if hj : j ∈ B then Pi.single ⟨j, hj⟩ 1 else co j
  have ha : ∀ b : B, a b.1 = Pi.single b 1 := fun b => by simp [a, b.2]
  let Dv : Fin (N + 1) → (EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) := fun j => fderiv ℂ (fun z => v j (c z)) 0
  have hDa : ∀ j : {j : Fin (N + 1) // j ≠ j0}, Dv j.1 = ∑ b, pt x (a j b) • Dv b.1.1 := by
    intro j
    by_cases hj : j ∈ B
    · simp only [a, dif_pos hj]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
    · simp only [a, dif_neg hj]; exact hco j
  have hxU' : c 0 ∈ U := by rw [hc0]; exact hxU.2
  have hDv : ∀ j, HasFDerivAt (fun z => v j (c z)) (Dv j) 0 := fun j =>
    ((hvd j (c 0) hxU').comp 0 (hc 0)).hasFDerivAt
  have hevU : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), c z ∈ U :=
    hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU')
  have hD0 : Dv j0 = 0 := by
    have h1 : HasFDerivAt (fun z => v j0 (c z)) (0 : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) 0 :=
      (hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq
        (hevU.mono fun z hz => by rw [hv]; exact div_self hz.2)
    exact (hDv j0).unique h1
  have hall : ∀ ξ, (∀ b : B, Dv b.1.1 ξ = 0) → ∀ j, Dv j ξ = 0 := by
    intro ξ hξ j
    by_cases hj : j = j0
    · rw [hj, hD0]; rfl
    · rw [hDa ⟨j, hj⟩, ContinuousLinearMap.sum_apply]
      exact Finset.sum_eq_zero fun b _ => by rw [ContinuousLinearMap.smul_apply, hξ b, smul_zero]

  let eqv := (EuclideanSpace.equiv (Fin n) ℂ).symm
  let Lc : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (eqv : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp (ContinuousLinearMap.pi fun k => Dv (jj k))
  have hLc : HasFDerivAt (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) Lc 0 := by
    have h1 : HasFDerivAt (fun z => fun k => v (jj k) (c z)) (ContinuousLinearMap.pi fun k => Dv (jj k)) 0 :=
      hasFDerivAt_pi.2 fun k => hDv (jj k)
    have hfun : (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
        W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) = eqv ∘ fun z => fun k => v (jj k) (c z) := by
      rw [hv]; rfl
    rw [hfun]
    exact eqv.hasFDerivAt.comp 0 h1
  rw [hLc.fderiv] at hJ
  have hLc_inj : Function.Injective Lc := by
    have h1 : IsUnit (Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJ)
    exact ((Module.End.isUnit_iff _).mp h1).injective
  have key : ∀ ξ, (∀ b : B, Dv b.1.1 ξ = 0) → ξ = 0 := by
    intro ξ hξ
    apply hLc_inj
    rw [map_zero]
    have h2 : (fun k => Dv (jj k) ξ) = 0 := funext fun k => hall ξ hξ (jj k)
    show eqv (fun k => Dv (jj k) ξ) = 0
    rw [h2, map_zero]

  have hcard1 : Fintype.card B ≤ n := by
    have h := hyB.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fintype] at h
    exact_mod_cast h
  have hcard2 : n ≤ Fintype.card B := by
    let Φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (B → ℂ) :=
      (ContinuousLinearMap.pi fun b : B => Dv b.1.1 : EuclideanSpace ℂ (Fin n) →L[ℂ] (B → ℂ)).toLinearMap
    have hinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro ξ hξ
      exact key ξ fun b => congrFun hξ b
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using h
  have hcardB : Fintype.card B = n := le_antisymm hcard1 hcard2
  have hyT : IsTranscendenceBasis K yB :=
    hyB.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fintype, hcardB])
  let e : Fin n ≃ B := (Fintype.equivFinOfCardEq hcardB).symm
  have hrelx : ∀ i : Fin n, ∑ j, t (i.succ, j) * pt x (u j) = 0 := by
    intro i
    have h := hs i
    have h2 : ∑ j, t (i.succ, j) * W j x = (∑ j, t (i.succ, j) * pt x (u j)) * W j0 x := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hWu x hx j]; ring
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_right hx0
  have hdet := SCoE.det_ne sg (pt x) (hpt x hx) j0 u hu0 B hyT e a ha t ht hrelx
  have hDv' : ∀ j, HasFDerivAt (fun z => W j (c z) / W j0 (c z)) (Dv j) 0 := by
    intro j; have h := hDv j; rw [hv] at h; exact h
  clear_value e a Dv
  refine ⟨Dv, hDv', ?_⟩
  refine ⟨_, fun k => Dv (e k).1.1, hdet, ?_, ?_⟩
  · intro ξ hξ
    apply key
    intro b
    have h1 : Dv (e (e.symm b)).1.1 ξ = 0 := hξ (e.symm b)
    rwa [Equiv.apply_symm_apply] at h1
  · intro i
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j0, hD0, smul_zero, zero_add]
    have hj : ∀ j : {j : Fin (N + 1) // j ≠ j0}, t (i.succ, j.1) • Dv j.1 =
        ∑ b, (t (i.succ, j.1) * pt x (a j b)) • Dv b.1.1 := fun j => by
      rw [hDa j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_smul]
    exact (e.sum_comp (fun b => ∑ j : {j : Fin (N + 1) // j ≠ j0}, (t (i.succ, j.1) * pt x (a j b)) • Dv b.1.1)).symm

theorem core {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    {Fr : Type} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr] {n N D : ℕ} (hD : n = D) (sg : K →+* ℂ)
    {dom Gen : Set Fr} (hdom : IsOpen dom) (hGs : Gen ⊆ dom) (hGd : dom ⊆ closure Gen)
    (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (htr : Algebra.trdeg K Ω = D)
    (W : Fin (N + 1) → Fr → ℂ) (hW : ∀ j, DifferentiableOn ℂ (W j) dom)
    (u : Fin (N + 1) → Ω) (j0 : Fin (N + 1)) (hWu : ∀ y ∈ Gen, ∀ j, W j y = pt y (u j) * W j0 y)
    (c : EuclideanSpace ℂ (Fin n) → Fr) (hc : Differentiable ℂ c) {x : Fr} (hc0 : c 0 = x)
    (hx : x ∈ Gen) (hx0 : W j0 x ≠ 0) (jj : Fin n → Fin (N + 1))
    (hJ : (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun k =>
      W (jj k) (c z) / W j0 (c z) : EuclideanSpace ℂ (Fin n))) 0).det ≠ 0)
    (t : Fin (D + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hs : ∀ i : Fin n, ∑ j, t ((Fin.cast hD i).succ, j) * W j x = 0)
    (hw : ∑ j, t (0, j) * W j x ≠ 0) :
    (fderiv ℂ (fun z : EuclideanSpace ℂ (Fin n) => (WithLp.toLp 2 fun i =>
      (∑ j, t ((Fin.cast hD i).succ, j) * W j (c z)) / (∑ j, t (0, j) * W j (c z)) :
        EuclideanSpace ℂ (Fin n))) 0).det ≠ 0 := by
  subst hD
  obtain ⟨Dv, hDv, M, w, hM, key, hrow⟩ :=
    part1 rfl sg hdom hGs hGd pt hpt htr W hW u j0 hWu c hc hc0 hx hx0 jj hJ t ht hs
  simp only [Fin.cast_eq_self] at hrow hs ⊢
  have hxd : c 0 ∈ dom := by rw [hc0]; exact hGs hx
  have hcx : ContinuousAt (fun z => W j0 (c z)) 0 :=
    ((hW j0).differentiableAt (hdom.mem_nhds hxd)).continuousAt.comp (hc 0).continuousAt
  have hx0' : W j0 (c 0) ≠ 0 := by rw [hc0]; exact hx0
  have hev : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin n)), W j0 (c z) ≠ 0 := hcx.eventually_ne hx0'
  have hw' : ∑ j, t (0, j) * W j (c 0) ≠ 0 := by rw [hc0]; exact hw
  have hT := SCoG.target W c j0 hev Dv hDv t hx0' (by rw [hc0]; exact hs) hw'
  rw [hT.fderiv]
  exact SCoG.finale Dv t M w hM key hrow _ (div_ne_zero hw' hx0')

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoF
