import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem rorth_apply_mem_genSub (a b : Fin n) {y : M} (hy : y ∈ genSub E V) :
    E a b y ∈ genSub E V := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro T hT
  exact hT.2 a b y (hy T hT)

theorem rorth_le_genSub : V ≤ genSub E V := by
  unfold genSub
  exact le_sInf fun T hT => hT.1

theorem rorth_functional_eq_zero (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (f : M →ₗ[ℂ] ℂ) (hfV : ∀ v ∈ V, f v = 0)
    (hfd : ∀ a y, f (E a a y) = (lowK ε lam a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y, f (E b a y) = 0) :
    ∀ y ∈ genSub E V, f y = 0 := by
  intro y hy
  rw [genSub_eq_iSup_layer hE hV.2.1,
    Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ h => layer_mono h)] at hy
  obtain ⟨k, hk⟩ := hy
  set W := layer ε E V k with hW
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 k
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : IsKStableSub ε E W := layer_kStable hE hV.2.1 k
  obtain ⟨u, hu⟩ : ∃ u : W, ∀ w : W, inner ℂ (u : M) (w : M) = f w := by
    refine ⟨(InnerProductSpace.toDual ℂ W).symm
      (LinearMap.toContinuousLinearMap (f.comp W.subtype)), fun w => ?_⟩
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := w)
      (y := LinearMap.toContinuousLinearMap (f.comp W.subtype))
    exact this
  have hsg : ∀ a b, ε a = ε b → adjSign ε a b = 1 := fun a b h => by simp [adjSign, h]
  have hkhw : IsKHWVec ε E (lowK ε lam) (u : M) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · have hz : E a a u - (lowK ε lam a : ℂ) • (u : M) ∈ W :=
        W.sub_mem (hWK a a rfl _ u.2) (W.smul_mem _ u.2)
      rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
      have key : ∀ z ∈ W, inner ℂ (E a a u - (lowK ε lam a : ℂ) • (u : M)) z = 0 := by
        intro z hz
        rw [inner_sub_left, inner_smul_left, hU a a, hsg a a rfl, one_mul,
          hu ⟨_, hWK a a rfl _ hz⟩, hu ⟨z, hz⟩]
        simp [hfd]
      exact key _ hz
    · have hz : E a b u ∈ W := hWK a b h _ u.2
      rw [← inner_self_eq_zero (𝕜 := ℂ), hU a b, hsg a b h, one_mul]
      exact (hu ⟨_, hWK b a h.symm _ hz⟩).trans (hfl a b hab h _)
  have huV : (u : M) ∈ V := khw_lowK_mem hE hU hV hc hgap (layer_le_genSub k u.2) hkhw
  have hu0 : (u : M) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hu u]
    exact hfV _ huV
  rw [← hu ⟨y, hk⟩, hu0, inner_zero_left]

end Alg

section Mat

theorem rorth_actM_add {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem rorth_actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    actM E (c • X) = c • actM E X := by
  simp only [actM, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

theorem rorth_actM_single {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply_same]
  · intro b' _ hb; rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), zero_smul]
  · simp
  · intro a' _ ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm ha), zero_smul]
  · simp

theorem rorth_mem_UJset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff'.1 hu)
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem rorth_inK_of_skew {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (h1 : Zᴴ = -Z)
    (h2 : Z * Jm ε = Jm ε * Z) : inK ε Z := by
  refine ⟨?_, h2⟩
  unfold inG
  rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

theorem rorth_inK_smul {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (t : ℝ) :
    inK ε ((t : ℂ) • Z) := by
  obtain ⟨h1, h2⟩ := hZ
  refine ⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩
  unfold inG at h1 ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

theorem rorth_single_comm {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i j
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [hij]

theorem rorth_inK_comb {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    inK ε (c • Matrix.single a b (1 : ℂ) + (-star c) • Matrix.single b a (1 : ℂ)) := by
  apply rorth_inK_of_skew
  · simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_single,
      star_one, star_star, neg_smul, Matrix.conjTranspose_neg, neg_add_rev, neg_neg]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, rorth_single_comm h, rorth_single_comm h.symm]

end Mat

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem rorth_inner_map (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y :=
  (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map x y

theorem rorth_exists_ext (hVf : FiniteDimensional ℂ V) (j : V →ₗ[ℂ] H) :
    ∃ φ : H →L[ℂ] H, ∀ v : V, φ ((v : D) : H) = j v := by
  let ι : V →ₗ[ℂ] H := D.subtype.comp V.subtype
  have hι : Function.Injective ι := D.injective_subtype.comp V.injective_subtype
  let S : Submodule ℂ H := LinearMap.range ι
  have : FiniteDimensional ℂ S := inferInstance
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let e : V ≃ₗ[ℂ] S := LinearEquiv.ofInjective ι hι
  refine ⟨(LinearMap.toContinuousLinearMap (j.comp e.symm.toLinearMap)).comp
    S.orthogonalProjectionOnto, fun v => ?_⟩
  have h1 : S.orthogonalProjectionOnto ((v : D) : H) = e v :=
    S.orthogonalProjectionOnto_mem_subspace_eq_self (e v)
  simp [h1]

theorem rorth_inner_actM (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (v : V) (x : D) :
    inner ℂ (j v) ((actM E Z x : D) : H) + inner ℂ (φ ((actM E Z v : D) : H)) (x : H) = 0 := by
  have h1 := hD.deriv Z hZ.1 (v : D)
  have h2 := hD.deriv Z hZ.1 x
  have h1' := (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := HasDerivAt.inner ℂ h1' h2
  have hconst : (fun t : ℝ => inner ℂ
      (((φ.restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) ((v : D) : H)) t)
      (σ (NormedSpace.exp ((t : ℂ) • Z)) (x : H))) = fun _ => inner ℂ (j v) (x : H) := by
    funext t
    have hk := exp_mem_Kset (rorth_inK_smul hZ t)
    obtain ⟨w, hw, hwe⟩ := hVK _ hk v v.2
    have h4 := hj _ hk v ⟨w, hw⟩ hwe
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← hwe, hφ ⟨w, hw⟩, h4, rorth_inner_map hσ (rorth_mem_UJset hk)]
  rw [hconst] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', exp_zero_smul, hσ.1.1,
    one_apply_eq_self, hφ] at h5
  exact h5

theorem rorth_inner_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {a b : Fin n} (h : ε a = ε b) (v : V) (x : D) :
    inner ℂ (φ ((E a b v : D) : H)) (x : H) = inner ℂ (j v) ((E b a x : D) : H) := by
  have h1 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h 1) v x
  have h2 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h Complex.I) v x
  simp only [rorth_actM_add, rorth_actM_smul, rorth_actM_single, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, star_one, map_one, map_neg,
    Complex.star_def, Complex.conj_I, neg_neg] at h1 h2
  have hI := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 -
    (1 / 2 : ℂ) * (inner ℂ (j v) ((E a b x : D) : H) + inner ℂ (j v) ((E b a x : D) : H) -
      inner ℂ (φ ((E a b v : D) : H)) (x : H) - inner ℂ (φ ((E b a v : D) : H)) (x : H)) * hI

theorem rigid_orth_genSub {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ y ∈ genSub E V, inner ℂ (j v') (y : H) = 0 := by
  obtain ⟨φ, hφ⟩ := rorth_exists_ext hV.1 j
  have hrel := fun a b (h : ε a = ε b) => rorth_inner_E hσ hD hVK j hj φ hφ h
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have h0 : ∀ y ∈ genSub E V, inner ℂ (j ⟨w, hwV⟩) (y : H) = 0 := by
    refine rorth_functional_eq_zero hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap
      ((innerₛₗ ℂ (j ⟨w, hwV⟩)).comp D.subtype) (fun v hv => horth ⟨v, hv⟩ _) (fun a y => ?_)
      (fun a b hab h y => ?_)
    · have := hrel a a rfl ⟨w, hwV⟩ y
      simp only [hw.1 a, Submodule.coe_smul, map_smul, inner_smul_left, Complex.conj_ofReal,
        hφ ⟨w, hwV⟩] at this
      exact this.symm
    · have := hrel a b h ⟨w, hwV⟩ y
      simp only [hw.2 a b hab h, Submodule.coe_zero, map_zero, inner_zero_left] at this
      exact this.symm
  let S : Submodule ℂ D :=
    { carrier := {v | v ∈ V ∧ ∀ y ∈ genSub E V, inner ℂ (φ (v : H)) (y : H) = 0}
      add_mem' := fun {u v} hu hv => ⟨V.add_mem hu.1 hv.1, fun y hy => by
        simp [hu.2 y hy, hv.2 y hy]⟩
      zero_mem' := ⟨V.zero_mem, fun y _ => by simp⟩
      smul_mem' := fun c v hv => ⟨V.smul_mem c hv.1, fun y hy => by
        simp [hv.2 y hy]⟩ }
  have hSK : IsKStableSub ε E S := by
    intro a b h v hv
    refine ⟨hV.2.1 a b h v hv.1, fun y hy => ?_⟩
    rw [hrel a b h ⟨v, hv.1⟩ y, ← hφ]
    exact hv.2 _ (rorth_apply_mem_genSub b a hy)
  have hwS : w ∈ S := ⟨hwV, fun y hy => by rw [hφ ⟨w, hwV⟩]; exact h0 y hy⟩
  rcases hV.2.2.1 S (fun v hv => hv.1) hSK with h | h
  · rw [h] at hwS
    exact absurd ((Submodule.mem_bot ℂ).1 hwS) hw0
  · intro v' y hy
    have hv' : (v' : D) ∈ S := by rw [h]; exact v'.2
    rw [← hφ]
    exact hv'.2 y hy

theorem rigid_orth_closure {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure, inner ℂ (j v') x = 0 := by
  intro v' x hx
  have hle : ((genSub E V).map D.subtype).topologicalClosure ≤ (ℂ ∙ j v')ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (rigid_orth_genSub hgap hσ hD hV hc hVK j hj horth v' y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx)

end Rep

end ReciprocityTheory.ChartRestriction.DS
