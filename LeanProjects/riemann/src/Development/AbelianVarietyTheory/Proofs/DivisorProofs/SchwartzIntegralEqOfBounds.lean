import Mathlib
open MeasureTheory

namespace GlobalTheory.SchwartzFormIntegral

open scoped BoundedContinuousFunction

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable def weightedDeriv (m n : ℕ) (φ : SchwartzMap D ℂ) :
    D →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n => D) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ m) • iteratedFDeriv ℝ n φ x)
    ((continuous_norm.pow m).smul ((φ.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)))
    (SchwartzMap.seminorm ℂ m n φ)
    (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact SchwartzMap.le_seminorm ℂ m n φ x)

lemma weightedDeriv_apply (m n : ℕ) (φ : SchwartzMap D ℂ) (x : D) :
    weightedDeriv m n φ x = (‖x‖ ^ m) • iteratedFDeriv ℝ n φ x := rfl

lemma norm_weightedDeriv_le (m n : ℕ) (φ : SchwartzMap D ℂ) :
    ‖weightedDeriv m n φ‖ ≤ SchwartzMap.seminorm ℂ m n φ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _

lemma seminorm_le_norm_weightedDeriv (m n : ℕ) (φ : SchwartzMap D ℂ) :
    SchwartzMap.seminorm ℂ m n φ ≤ ‖weightedDeriv m n φ‖ :=
  SchwartzMap.seminorm_le_bound ℂ m n φ (norm_nonneg _) (fun x => by
    have := (weightedDeriv m n φ).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_of_nonneg (by positivity)] at this)

abbrev Target (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D] (N : ℕ) :=
  (m : Fin (N + 1)) → (n : Fin (N + 1)) →
    (D →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => D) ℂ)

noncomputable def embLin (N : ℕ) : SchwartzMap D ℂ →ₗ[ℂ] Target D N where
  toFun φ m n := weightedDeriv m n φ
  map_add' φ ψ := by
    funext m n; ext x : 1
    have e : (⇑(φ + ψ) : D → ℂ) = ⇑φ + ⇑ψ := rfl
    simp only [Pi.add_apply, BoundedContinuousFunction.coe_add, weightedDeriv_apply, e]
    rw [iteratedFDeriv_add_apply ((φ.smooth ⊤).of_le (mod_cast le_top)).contDiffAt
      ((ψ.smooth ⊤).of_le (mod_cast le_top)).contDiffAt, smul_add]
  map_smul' a φ := by
    funext m n; ext x : 1
    have e : (⇑(a • φ) : D → ℂ) = a • ⇑φ := rfl
    simp only [Pi.smul_apply, BoundedContinuousFunction.coe_smul, weightedDeriv_apply, e,
      RingHom.id_apply]
    rw [iteratedFDeriv_const_smul_apply ((φ.smooth ⊤).of_le (mod_cast le_top)).contDiffAt,
      smul_comm]

lemma norm_embLin_le (N : ℕ) (φ : SchwartzMap D ℂ) :
    ‖embLin N φ‖ ≤ ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1),
      SchwartzMap.seminorm ℂ m n φ := by
  have h0 : ∀ m n, 0 ≤ SchwartzMap.seminorm ℂ m n φ := fun m n => apply_nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun n => ?_
  refine (norm_weightedDeriv_le m n φ).trans ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => h0 i j)
    (Finset.mem_range.2 m.2))
  exact Finset.single_le_sum (fun j _ => h0 _ j) (Finset.mem_range.2 n.2)

noncomputable def emb (N : ℕ) : SchwartzMap D ℂ →L[ℂ] Target D N :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (embLin N) (map_add _) (map_smul _)
    ⟨Finset.range (N + 1) ×ˢ Finset.range (N + 1), 1, zero_le_one, fun φ => by
      rw [one_mul]
      refine (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).2 fun m => ?_
      refine (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).2 fun n => ?_
      refine (norm_weightedDeriv_le m n φ).trans ?_
      exact Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ D ℂ) (i := ((m : ℕ), (n : ℕ)))
        (Finset.mem_product.2 ⟨Finset.mem_range.2 m.2, Finset.mem_range.2 n.2⟩)⟩

lemma embLin_injective (N : ℕ) : Function.Injective (embLin (D := D) N) := by
  rw [injective_iff_map_eq_zero]
  intro φ h
  ext x
  have h1 : weightedDeriv 0 0 φ = 0 := congrFun (congrFun h 0) 0
  have h2 := congrArg (fun g => g x (fun _ => x)) h1
  simpa [weightedDeriv_apply] using h2

lemma exists_factor {E B : Type} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup B]
    [NormedSpace ℂ B] (ι : E →ₗ[ℂ] B) (hι : Function.Injective ι) (T : E →ₗ[ℂ] ℂ) (C : ℝ)
    (h : ∀ φ, ‖T φ‖ ≤ C * ‖ι φ‖) : ∃ T' : B →L[ℂ] ℂ, ∀ φ, T' (ι φ) = T φ := by
  let e := LinearEquiv.ofInjective ι hι
  have he : ∀ y : LinearMap.range ι, ι (e.symm y) = y := fun y => by
    have : ((e (e.symm y) : LinearMap.range ι) : B) = ι (e.symm y) := rfl
    rw [← this, e.apply_symm_apply]
  let g : LinearMap.range ι →L[ℂ] ℂ := (T ∘ₗ e.symm.toLinearMap).mkContinuous C (fun y => by
    have := h (e.symm y)
    rw [he] at this
    exact this)
  obtain ⟨T', hT', -⟩ := exists_extension_norm_eq (LinearMap.range ι) g
  refine ⟨T', fun φ => ?_⟩
  have := hT' (e φ)
  refine this.trans ?_
  change T (e.symm (e φ)) = T φ
  rw [e.symm_apply_apply]

lemma exists_bound (T : SchwartzMap D ℂ →L[ℂ] ℂ) :
    ∃ (N : ℕ) (C : ℝ), ∀ φ, ‖T φ‖ ≤ C * ‖embLin N φ‖ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ D ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (T.continuous.norm)
  refine ⟨s.sup (fun p => max p.1 p.2), C, fun φ => ?_⟩
  refine (hC φ).trans ?_
  change (C : ℝ) * _ ≤ _
  refine mul_le_mul_of_nonneg_left ?_ C.2
  refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun p hp => ?_
  have hle : max p.1 p.2 ≤ s.sup (fun p => max p.1 p.2) :=
    Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
  refine (seminorm_le_norm_weightedDeriv p.1 p.2 φ).trans ?_
  exact (norm_le_pi_norm (embLin (s.sup (fun p => max p.1 p.2)) φ ⟨p.1, by omega⟩)
    ⟨p.2, by omega⟩).trans (norm_le_pi_norm _ _)

theorem form_integral_comm : ∀ {D S : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S) (f : S → SchwartzMap D ℂ)
    (F : SchwartzMap D ℂ),
    Continuous f →
    (∀ m n : ℕ, ∃ c : S → ℝ, Integrable c ν ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) →
    (∀ (n : ℕ) (x : D), iteratedFDeriv ℝ n F x = ∫ s, iteratedFDeriv ℝ n (f s) x ∂ν) →
    ∀ T : SchwartzMap D ℂ →L[ℂ] ℂ, T F = ∫ s, T (f s) ∂ν := by
  intro D S _ _ _ _ _ _ ν f F hf hc hF T
  obtain ⟨N, C, hC⟩ := exists_bound T
  obtain ⟨T', hT'⟩ := exists_factor (embLin N) (embLin_injective N) T.toLinearMap C hC
  choose c hc1 hc2 using hc
  haveI : SecondCountableTopologyEither S (Target D N) := ⟨Or.inl inferInstance⟩
  have hint : Integrable (fun s => emb N (f s)) ν := by
    refine Integrable.mono' (g := fun s => ∑ m ∈ Finset.range (N + 1),
      ∑ n ∈ Finset.range (N + 1), c m n s) ?_
      ((emb N).continuous.comp hf).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    · exact integrable_finset_sum _ fun m _ => integrable_finset_sum _ fun n _ => hc1 m n
    · refine (norm_embLin_le N (f s)).trans ?_
      exact Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => hc2 m n s
  have hE : emb N F = ∫ s, emb N (f s) ∂ν := by
    funext m n
    ext x : 1
    let L : Target D N →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => D) ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ x).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun n : Fin (N + 1) =>
            D →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => D) ℂ) n).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (N + 1) => (n : Fin (N + 1)) →
            D →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin (n : ℕ) => D) ℂ) m))
    have h1 := L.integral_comp_comm hint
    change _ = L _
    rw [← h1]
    change (‖x‖ ^ (m : ℕ)) • iteratedFDeriv ℝ n F x =
      ∫ s, (‖x‖ ^ (m : ℕ)) • iteratedFDeriv ℝ n (f s) x ∂ν
    rw [integral_smul, hF]
  calc T F = T' (emb N F) := (hT' F).symm
    _ = ∫ s, T' (emb N (f s)) ∂ν := by rw [hE, T'.integral_comp_comm hint]
    _ = ∫ s, T (f s) ∂ν := by
      congr 1
      funext s
      exact hT' (f s)

end GlobalTheory.SchwartzFormIntegral
