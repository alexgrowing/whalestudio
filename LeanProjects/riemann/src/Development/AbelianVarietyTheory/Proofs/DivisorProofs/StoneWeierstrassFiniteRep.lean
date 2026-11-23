import Mathlib

open MeasureTheory

namespace GlobalTheory

theorem continuous_integral_continuousMap_compact {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] (μ : Measure K) [IsProbabilityMeasure μ] :
    Continuous (fun F : C(K, ℂ) => ∫ q, F q ∂μ) := by
  have hint : ∀ F : C(K, ℂ), Integrable F μ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun F G => ?_).continuous
  rw [dist_eq_norm, ← integral_sub (hint F) (hint G)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun q => F q - G q) (C := dist F G)
    (Filter.Eventually.of_forall fun q => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist q)
  simpa using this

theorem integral_translate_mem_of_finiteDimensional {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (Q : Subgroup G) [CompactSpace Q] [MeasurableSpace Q]
    [OpensMeasurableSpace Q] (μ : Measure Q) [IsProbabilityMeasure μ]
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ w ∈ V, ∀ q ∈ Q, (fun g => w (q * g)) ∈ V) (P : G → ℂ) (hP : P ∈ V)
    (hPc : Continuous P) (c : Q → ℂ) (hc : Continuous c) :
    (fun g => ∫ q, c q * P (((q⁻¹ : Q) : G) * g) ∂μ) ∈ V := by
  let b := Module.finBasis ℂ V
  let φ : Q → V := fun q => ⟨fun g => P (((q⁻¹ : Q) : G) * g), hV P hP _ (q⁻¹).2⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk (continuous_pi fun g => hPc.comp ?_) _
    fun_prop
  have hco : ∀ l, Continuous fun q => b.coord l (φ q) := fun l =>
    (LinearMap.continuous_of_finiteDimensional (b.coord l)).comp hφ
  have hexp : ∀ q g, P (((q⁻¹ : Q) : G) * g) = ∑ l, b.coord l (φ q) * (b l : G → ℂ) g := by
    intro q g
    have h := congrArg (fun w : V => (w : G → ℂ) g) (b.sum_repr (φ q))
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  have key : (fun g => ∫ q, c q * P (((q⁻¹ : Q) : G) * g) ∂μ) =
      ∑ l, (∫ q, c q * b.coord l (φ q) ∂μ) • (b l : G → ℂ) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hexp, Finset.mul_sum]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [← integral_mul_const]
      simp only [mul_assoc]
    · intro l _
      exact (hc.mul ((hco l).mul continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [key]
  exact V.sum_mem fun l _ => V.smul_mem _ (b l).2

theorem exists_equivariant_mem_subalgebra_of_compact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Q : Subgroup G), IsCompact (Q : Set G) →
    ∀ (d : ℕ) (ρ : Q →* Matrix (Fin d) (Fin d) ℂ), Continuous ρ → ∀ A : Subalgebra ℂ (G → ℂ), (∀ f ∈ A, Continuous f) → (∀ f ∈ A, star f ∈ A) →
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ∃ f ∈ A, f x ≠ f y) →
      (∀ f ∈ A, ∃ V : Submodule ℂ (G → ℂ), FiniteDimensional ℂ V ∧ f ∈ V ∧ (∀ w ∈ V, w ∈ A) ∧ ∀ w ∈ V, ∀ q ∈ Q, (fun g => w (q * g)) ∈ V) →
      ∀ v : Fin d → ℂ, ∃ f : Fin d → G → ℂ, (∀ i, f i ∈ A) ∧ (∀ i, f i 1 = v i) ∧
        ∀ (q : Q) (g : G), (fun i => f i ((q : G) * g)) = Matrix.mulVec (ρ q) (fun i => f i g) := by
  intro G _ _ _ _ Q hQ d ρ hρ A hAc hAs hsep hfin v
  haveI : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  letI : MeasurableSpace Q := borel Q
  haveI : BorelSpace Q := ⟨rfl⟩
  let μ : Measure Q := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := Q) (K₀ := ⊤)
    simpa using this⟩
  have hint : ∀ f : Q → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρc : ∀ i j, Continuous fun q => ρ q i j := fun i j => hρ.matrix_elem i j
  let S : Submodule ℂ (Fin d → ℂ) :=
    { carrier := {v | ∃ f : Fin d → G → ℂ, (∀ i, f i ∈ A) ∧ (∀ i, f i 1 = v i) ∧
        ∀ (q : Q) (g : G), (fun i => f i ((q : G) * g)) = Matrix.mulVec (ρ q) (fun i => f i g)}
      zero_mem' := ⟨0, fun _ => A.zero_mem, fun _ => rfl, fun q g => by
        funext i; simp [Matrix.mulVec, dotProduct]⟩
      add_mem' := by
        rintro v w ⟨f, hf1, hf2, hf3⟩ ⟨h, hh1, hh2, hh3⟩
        refine ⟨f + h, fun i => A.add_mem (hf1 i) (hh1 i), fun i => by simp [hf2, hh2],
          fun q g => ?_⟩
        have : (fun i => (f + h) i g) = (fun i => f i g) + (fun i => h i g) := rfl
        rw [this, Matrix.mulVec_add, ← hf3, ← hh3]; rfl
      smul_mem' := by
        rintro c v ⟨f, hf1, hf2, hf3⟩
        refine ⟨c • f, fun i => A.smul_mem (hf1 i) c, fun i => by simp [hf2], fun q g => ?_⟩
        have : (fun i => (c • f) i g) = c • (fun i => f i g) := rfl
        rw [this, Matrix.mulVec_smul, ← hf3]; rfl }
  change v ∈ S
  have hS : IsClosed (S : Set (Fin d → ℂ)) := S.closed_of_finiteDimensional
  let r : Fin d → Fin d → C(Q, ℂ) := fun i j => ⟨fun q => ρ q i j, hρc i j⟩
  let ι : C(Q, Q) := ⟨fun q => q⁻¹, continuous_inv⟩
  let Φ : (Fin d → C(Q, ℂ)) → (Fin d → ℂ) := fun F i =>
    ∑ j, ∫ q, (r i j * (F j).comp ι) q ∂μ
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_finset_sum _ fun j _ => ?_
    refine (continuous_integral_continuousMap_compact μ).comp ?_
    exact continuous_const.mul ((ContinuousMap.continuous_precomp ι).comp (continuous_apply j))
  let B : StarSubalgebra ℂ C(Q, ℂ) :=
    { carrier := {F | ∃ P ∈ A, ∀ q : Q, F q = P q}
      mul_mem' := by
        rintro F H ⟨P, hP, h1⟩ ⟨R, hR, h2⟩
        exact ⟨P * R, A.mul_mem hP hR, fun q => by simp [h1, h2]⟩
      add_mem' := by
        rintro F H ⟨P, hP, h1⟩ ⟨R, hR, h2⟩
        exact ⟨P + R, A.add_mem hP hR, fun q => by simp [h1, h2]⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ _ c, A.algebraMap_mem c, fun q => rfl⟩
      star_mem' := by
        rintro F ⟨P, hP, h1⟩
        exact ⟨star P, hAs P hP, fun q => by simp [h1]⟩ }
  have hBsep : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hne⟩ := hsep x x.2 y y.2 (fun h => hxy (Subtype.ext h))
    exact ⟨_, ⟨⟨fun q : Q => f q, (hAc f hf).comp continuous_subtype_val⟩,
      ⟨f, hf, fun _ => rfl⟩, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hBsep
  have hBd : Dense (B : Set C(Q, ℂ)) := by
    intro F
    have : F ∈ B.topologicalClosure := htop ▸ StarSubalgebra.mem_top
    exact this
  have hdense : Dense (Set.pi Set.univ fun _ : Fin d => (B : Set C(Q, ℂ))) :=
    dense_pi Set.univ fun _ _ => hBd
  have hmem : ∀ F ∈ Set.pi Set.univ fun _ : Fin d => (B : Set C(Q, ℂ)), Φ F ∈ S := by
    intro F hF
    have hF' : ∀ j, ∃ P ∈ A, ∀ q : Q, F j q = P q := fun j => hF j (Set.mem_univ j)
    choose P hPA hPF using hF'
    have hPc : ∀ j g, Continuous fun q : Q => P j (((q⁻¹ : Q) : G) * g) := fun j g =>
      (hAc _ (hPA j)).comp (by fun_prop)
    refine ⟨fun i g => ∑ j, ∫ q, ρ q i j * P j (((q⁻¹ : Q) : G) * g) ∂μ, fun i => ?_,
      fun i => ?_, fun q₀ g => ?_⟩
    · have : (fun g => ∑ j, ∫ q, ρ q i j * P j (((q⁻¹ : Q) : G) * g) ∂μ) =
          ∑ j, fun g => ∫ q, ρ q i j * P j (((q⁻¹ : Q) : G) * g) ∂μ := by
        funext g; simp only [Finset.sum_apply]
      beta_reduce
      rw [this]
      refine A.sum_mem fun j _ => ?_
      obtain ⟨V, hVf, hPV, hVA, hV⟩ := hfin _ (hPA j)
      exact hVA _ (integral_translate_mem_of_finiteDimensional Q μ V hV _ hPV (hAc _ (hPA j)) _
        (hρc i j))
    · simp only [Φ, r, ι, mul_one, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, hPF]
    · funext i
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_mul_left_eq_self _ q₀]
      simp only [← integral_const_mul]
      rw [← integral_finset_sum]
      swap
      · intro k _
        exact hint _ (continuous_const.mul ((hρc k j).mul (hPc j g)))
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [map_mul, Matrix.mul_apply, Finset.sum_mul, mul_inv_rev, Subgroup.coe_mul,
        Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  have hall : ∀ F, Φ F ∈ S := by
    intro F
    have h := closure_minimal (s := Set.pi Set.univ fun _ : Fin d => (B : Set C(Q, ℂ)))
      (t := Φ ⁻¹' S) hmem (hS.preimage hΦ)
    exact h (hdense F)
  let F₀ : Fin d → C(Q, ℂ) := fun j => ⟨fun q => ∑ k, ρ q j k * v k,
    continuous_finset_sum _ fun k _ => (hρc j k).mul continuous_const⟩
  have hv : Φ F₀ = v := by
    funext i
    simp only [Φ]
    rw [← integral_finset_sum _ fun j _ => hint _ (ContinuousMap.continuous _)]
    have : ∀ q : Q, ∑ j, (r i j * (F₀ j).comp ι) q = v i := by
      intro q
      have h : (ρ q).mulVec ((ρ q⁻¹).mulVec v) = v := by
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
      exact congrFun h i
    simp only [this]
    simp
  exact hv ▸ hall F₀

end GlobalTheory
