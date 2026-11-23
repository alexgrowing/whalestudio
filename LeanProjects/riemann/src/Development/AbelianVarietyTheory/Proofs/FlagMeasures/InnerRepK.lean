import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

variable {n : ℕ}

lemma toMK_cont (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

lemma inner_rep {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn G σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map (⟨(σ g : H →ₗ[ℂ] H), h.2.1 g hg⟩ : H →ₗᵢ[ℂ] H) x y

lemma inner_rep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (Kset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε) (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (star g) y⟫_ℂ := by
  rw [← inner_rep h hg x, ← ContinuousLinearMap.comp_apply (σ g) (σ (star g)), ← h.1.2 _ hg _ (Kset_star ε hg),
    Unitary.mul_star_self_of_mem hg.1, h.1.1, ContinuousLinearMap.one_apply]

theorem rangeType : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : S →L[ℂ] H'), IsKTypeOf ε σ abelian₂ S → (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ' k (T x)) → T ≠ 0 → IsKTypeOf ε σ' abelian₂ (LinearMap.range (T : S →ₗ[ℂ] H')) := by
  intro n ε abelian₂ H _ _ σ S H' _ _ σ' T hS hT hT0
  haveI := hS.1
  have hinj : Function.Injective T := by
    rcases hS.2.2.1 ((LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x = 0 := hx
      change T _ = 0
      rw [hT k hk x _ rfl, hx', map_zero]) with h | h
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · exfalso
      apply hT0
      ext x
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  have hT' : ∀ k (hk : k ∈ Kset ε) (x : S), σ' k (T x) = T ⟨σ k x, hS.2.1 k hk x x.2⟩ :=
    fun k hk x => (hT k hk x _ rfl).symm
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro k hk _ ⟨x, rfl⟩
    exact ⟨_, (hT' k hk x).symm⟩
  · intro S' hle hst
    rcases hS.2.2.1 ((S'.comap (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x ∈ S' := hx
      change T _ ∈ S'
      rw [← hT' k hk x]
      exact hst k hk _ hx') with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := hle hz
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hz, rfl⟩
      rw [h] at this
      have : x = 0 := Subtype.ext this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, rfl⟩
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨T ⟨v, hv⟩, ⟨_, rfl⟩, fun h => hv0 (congrArg Subtype.val (hinj (h.trans (map_zero T).symm))), ?_⟩
    intro θ hθ
    rw [← map_smul]
    exact (hT _ hθ ⟨v, hv⟩ _ (hwt θ hθ).symm).symm
  · rintro μ _ ⟨x, rfl⟩ h0 hwt
    refine hS.2.2.2.2 μ x x.2 (fun h => h0 (by have : x = 0 := Subtype.ext h; simp [this])) fun θ hθ => ?_
    have := hwt θ hθ
    change σ' _ (T x) = _ • T x at this
    rw [hT' _ hθ, ← map_smul] at this
    exact congrArg Subtype.val (hinj this)

theorem psEntry : PhiPos → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → (∀ v : W, ContinuousOn (fun k => τ k v) (Kset ε)) → ∀ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef → ∀ u y : W, ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  intro hP n ε lam W _ _ τ w hW hτ x hx u y
  haveI := FiniteDimensional.complete ℂ W
  have hk : Continuous (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) := (hτ w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finset_prod _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix _ _).matrix_det
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1))).1 i
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

theorem muConj : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), ∫ k : KG ε, F ((toMK k).map star) ∂(muK ε) = ∫ k : KG ε, F (toMK k) ∂(muK ε) := by
  intro n ε F
  let c0 : (Matrix (Fin n) (Fin n) ℂ)ˣ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom
  let c : KG ε → KG ε := fun k => ⟨⟨c0 k.1.1, UJ_star k.1.2⟩, K_star k.2⟩
  have hc : ∀ k, toMK (c k) = (toMK k).map star := fun k => rfl
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hcc : ∀ k, c (c k) = k := fun k => hemb.injective (by simp only [hc, map_star_star])
  have hcont : Continuous c := by
    rw [hemb.continuous_iff]
    exact hemb.continuous.matrix_map continuous_star
  let e : KG ε ≃ₜ* KG ε :=
    { toFun := c, invFun := c, left_inv := hcc, right_inv := hcc
      map_mul' := fun a b => hemb.injective (by
        change (toMK a * toMK b).map star = (toMK a).map star * (toMK b).map star
        exact map_star_mul _ _)
      continuous_toFun := hcont, continuous_invFun := hcont }
  haveI := (compact_haar_holds n ε).1
  haveI : IsProbabilityMeasure ((muK ε).map e) := Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
  haveI : ((muK ε).map e).IsHaarMeasure := e.isHaarMeasure_map _
  have h : (muK ε).map e = muK ε := Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have := integral_map_equiv (μ := muK ε) e.toHomeomorph.toMeasurableEquiv (fun k => F (toMK k))
  rw [show (muK ε).map e.toHomeomorph.toMeasurableEquiv = muK ε from h] at this
  exact this.symm

theorem avgMap : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (u : H), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → CompleteSpace H → IsURepOn (Kset ε) σ → ∃ T : W →L[ℂ] H, (∀ k ∈ Kset ε, ∀ x, T (ρ k x) = σ k (T x)) ∧ ∀ (x : W) (φ : H →L[ℂ] ℂ), Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u)) (muK ε) ∧ φ (T x) = ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u) ∂(muK ε) := by
  intro n ε W _ _ ρ w H _ _ σ u hW hρ hH hσ
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h2 : Continuous (fun k : KG ε => σ (toMK k) u) := (hσ.2.2 u).comp_continuous (toMK_cont ε) fun k => k.2
  have hi : ∀ x : W, Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u) (muK ε) := fun x =>
    ((h1.inner continuous_const).smul h2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : W →ₗ[ℂ] H :=
    { toFun := fun x => ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)
      map_add' := fun x y => by simp only [inner_add_right, add_smul]; exact integral_add (hi x) (hi y)
      map_smul' := fun c x => by simp only [inner_smul_right, mul_smul, integral_smul, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap T, fun k hk x => ?_, fun x φ => ⟨?_, ?_⟩⟩
  · obtain ⟨k0, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
    change ∫ k : KG ε, ⟪ρ (toMK k) w, ρ (toMK k0) x⟫_ℂ • σ (toMK k) u ∂(muK ε) =
      σ (toMK k0) (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x), ← integral_mul_left_eq_self _ k0]
    congr 1
    funext k
    have e : toMK (k0 * k) = toMK k0 * toMK k := rfl
    simp only [e, hρ.1.2 _ k0.2 _ k.2, hσ.1.2 _ k0.2 _ k.2, ContinuousLinearMap.comp_apply, inner_rep hρ k0.2,
      map_smul]
  · simpa using φ.integrable_comp (hi x)
  · change φ (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x)]
    simp

theorem avgSchur : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ W, IsKStableOn ε ρ S → S = ⊥ ∨ S = ⊤) → w ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ (x : W) (φ : W →L[ℂ] ℂ), ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (ρ (toMK k) w) ∂(muK ε) = c * φ x := by
  intro n ε W _ _ ρ w hW hρ hirr hw
  haveI := FiniteDimensional.complete ℂ W
  haveI : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  obtain ⟨T, hT, hTi⟩ := avgMap n ε W ρ w W ρ w hW hρ inferInstance hρ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : W →ₗ[ℂ] W)
  have hTc : ∀ x, T x = c • x := by
    rcases hirr (Module.End.eigenspace (T : W →ₗ[ℂ] W) c) (fun k hk x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change T _ = _ at hx ⊢
      rw [hT k hk, hx, map_smul]) with h | h
    · exact absurd h hc
    · intro x
      have : x ∈ Module.End.eigenspace (T : W →ₗ[ℂ] W) c := by rw [h]; trivial
      exact Module.End.mem_eigenspace_iff.1 this
  refine ⟨c, ?_, fun x φ => by rw [← (hTi x φ).2, hTc, map_smul, smul_eq_mul]⟩
  rintro rfl
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h0 := (hTi w (innerSL ℂ w)).2
  rw [hTc, zero_smul, map_zero] at h0
  have e : ∀ k : KG ε, ⟪ρ (toMK k) w, w⟫_ℂ * innerSL ℂ w (ρ (toMK k) w) =
      ((‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [innerSL_apply_apply, ← inner_conj_symm, Complex.conj_mul']; simp
  simp only [e, integral_ofReal] at h0
  have hc2 : Continuous (fun k : KG ε => ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2) := (continuous_const.inner h1).norm.pow 2
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := 1)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by
      have : toMK (1 : KG ε) = 1 := rfl
      simpa [this, hρ.1.1] using hw)
  have : (0 : ℝ) = ∫ k : KG ε, ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) := by exact_mod_cast h0
  linarith

end GlobalTheory.Dec.FormF
