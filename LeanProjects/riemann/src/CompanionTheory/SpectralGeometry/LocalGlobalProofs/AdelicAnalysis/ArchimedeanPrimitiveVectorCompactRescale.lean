import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PrimInf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem reduce_of_equiv {K : Type} [CommRing K] [TopologicalSpace K] {W : Type} [Fintype W]
    (Φ : K ≃+* (W → ℂ)) (hΦ : IsHomeomorph Φ) (M : ℕ) :
    ∃ Ω : Set (Fin 1 → Fin M → K), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → K,
      (∃ z : Fin M → K, z ⬝ᵥ y 0 = 1) →
      ∃ (a : Kˣ) (z : Fin 1 → Fin M → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : K) • y) 0 = 1 := by
  classical
  let e : K ≃ₜ (W → ℂ) := hΦ.homeomorph
  have he : ∀ x, e x = Φ x := fun _ => rfl
  let H : (Fin 1 → Fin M → K) ≃ₜ (Fin 1 → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  let P : Set (Fin 1 → Fin M → W → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 1
  have hP : IsCompact P :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall 0 1
  have hmem : ∀ y, y ∈ H ⁻¹' P ↔ ∀ a i w, ‖Φ (y a i) w‖ ≤ 1 := by
    intro y
    simp only [Set.mem_preimage, P, Set.mem_pi, Set.mem_univ, true_imp_iff, mem_closedBall_zero_iff]
    rfl
  refine ⟨H ⁻¹' P, H.isCompact_preimage.mpr hP, ?_⟩
  rintro y ⟨z₀, hz₀⟩
  have hsum : ∀ w, ∑ i, Φ (z₀ i) w * Φ (y 0 i) w = 1 := by
    intro w
    have := congrFun (congrArg Φ hz₀) w
    simpa [dotProduct, map_sum, Finset.sum_apply] using this
  have hmax : ∀ w, ∃ i, (∀ j, ‖Φ (y 0 j) w‖ ≤ ‖Φ (y 0 i) w‖) ∧ Φ (y 0 i) w ≠ 0 := by
    intro w
    obtain ⟨i₀, hi₀⟩ : ∃ i, Φ (y 0 i) w ≠ 0 := by
      by_contra hall
      push_neg at hall
      have := hsum w
      simp [hall] at this
    haveI : Nonempty (Fin M) := ⟨i₀⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖Φ (y 0 j) w‖
    refine ⟨i, hi, fun h0 => hi₀ ?_⟩
    have := hi i₀
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.mp this
  choose I hI hI0 using hmax
  let u : W → ℂ := fun w => Φ (y 0 (I w)) w
  have hu : ∀ w, u w ≠ 0 := hI0
  let a : Kˣ :=
    { val := Φ.symm fun w => (u w)⁻¹
      inv := Φ.symm u
      val_inv := by
        apply Φ.injective
        funext w
        simp [hu w]
      inv_val := by
        apply Φ.injective
        funext w
        simp [hu w] }
  have hΦa : ∀ w, Φ (a : K) w = (u w)⁻¹ := fun w => by simp [a]
  let z : Fin 1 → Fin M → K := fun _ i => Φ.symm fun w => if I w = i then 1 else 0
  have hΦz : ∀ b i w, Φ (z b i) w = if I w = i then 1 else 0 := fun b i w => by simp [z]
  refine ⟨a, z, ?_, ?_, ?_⟩
  · rw [hmem]
    intro b i w
    obtain rfl : b = 0 := Subsingleton.elim _ _
    have : Φ (((a : K) • y) 0 i) w = (u w)⁻¹ * Φ (y 0 i) w := by
      simp [hΦa]
    rw [this, norm_mul, norm_inv]
    have hpos : 0 < ‖u w‖ := norm_pos_iff.mpr (hu w)
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hI w i
  · rw [hmem]
    intro b i w
    rw [hΦz b i w]
    split_ifs <;> simp
  · apply Φ.injective
    funext w
    have h1 : ∀ i, Φ (z 0 i) w * Φ (((a : K) • y) 0 i) w =
        if I w = i then (u w)⁻¹ * Φ (y 0 i) w else 0 := by
      intro i
      have : Φ (((a : K) • y) 0 i) w = (u w)⁻¹ * Φ (y 0 i) w := by simp [hΦa]
      rw [this, hΦz 0 i w]
      split_ifs <;> simp
    simp only [dotProduct, map_sum, Finset.sum_apply, map_mul, Pi.mul_apply, map_one, Pi.one_apply]
    rw [Finset.sum_congr rfl fun i _ => h1 i]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact inv_mul_cancel₀ (hu w)

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_delta (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
  obtain ⟨-, hC, -, hτ⟩ := h
  let τ₀ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have hnr : ¬ ComplexEmbedding.IsReal τ₀ := fun hr =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex (InfinitePlace.mk τ₀))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ₀ x
    rw [hall x] at this
    exact this.symm
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ₀.injective (by rw [hτ, hτ, star_star])
  refine ⟨x - σ x, by simp [hσσ], sub_ne_zero.mpr (Ne.symm hx)⟩

theorem exists_basis (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : s • (1 : E) - t • δ = 0 := by
      have := congrArg σ.toLinearMap hst
      rw [map_add, LinearMap.map_smul, LinearMap.map_smul, map_zero] at this
      simp only [AlgHom.toLinearMap_apply, map_one, hδ, smul_neg] at this
      rwa [sub_eq_add_neg]
    have h3 : (2 * t) • δ = 0 := by
      have : (2 * t) • δ = (s • (1 : E) + t • δ) - (s • (1 : E) - t • δ) := by
        rw [mul_smul, two_smul]
        abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · simpa using h4
      · exact absurd h4 h0
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [h.2.2.1]
    rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · simp
  · simp

theorem exists_tau (w : InfinitePlace F) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = w.embedding := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes x

end

section

variable {F : Type} [Field F] [NumberField F]

theorem exists_psi (ρ : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ) (hρc : ∀ w, Continuous (ρ w))
    (hρs : ∀ w, Continuous (ρ w).symm) (t : InfinitePlace F → ℂ) (htre : ∀ w, (t w).re = 0)
    (htim : ∀ w, (t w).im ≠ 0) :
    ∃ Ψ : (Fin 2 → Ainf F) ≃ₜ (InfinitePlace F → ℂ),
      ∀ p w, Ψ p w = ((ρ w (p 0 w) : ℝ) : ℂ) + ((ρ w (p 1 w) : ℝ) : ℂ) * t w := by
  let inv : (InfinitePlace F → ℂ) → Fin 2 → Ainf F := fun z k =>
    if k = 0 then fun w => (ρ w).symm (z w).re else fun w => (ρ w).symm ((z w).im / (t w).im)
  have hinv0 : ∀ z w, inv z 0 w = (ρ w).symm (z w).re := fun z w => rfl
  have hinv1 : ∀ z w, inv z 1 w = (ρ w).symm ((z w).im / (t w).im) := fun z w => rfl
  let fwd : (Fin 2 → Ainf F) → InfinitePlace F → ℂ :=
    fun p w => ((ρ w (p 0 w) : ℝ) : ℂ) + ((ρ w (p 1 w) : ℝ) : ℂ) * t w
  have hre : ∀ p w, (fwd p w).re = ρ w (p 0 w) := fun p w => by
    simp [fwd, htre w]
  have him : ∀ p w, (fwd p w).im = ρ w (p 1 w) * (t w).im := fun p w => by
    simp [fwd]
  have hl : Function.LeftInverse inv fwd := by
    intro p
    funext k
    revert k
    rw [Fin.forall_fin_two]
    constructor
    · funext w
      rw [hinv0, hre, RingEquiv.symm_apply_apply]
    · funext w
      rw [hinv1, him, mul_div_cancel_right₀ _ (htim w), RingEquiv.symm_apply_apply]
  have hr : Function.RightInverse inv fwd := by
    intro z
    funext w
    apply Complex.ext
    · rw [hre, hinv0, RingEquiv.apply_symm_apply]
    · rw [him, hinv1, RingEquiv.apply_symm_apply, div_mul_cancel₀ _ (htim w)]
  have hc1 : Continuous fwd := by
    refine continuous_pi fun w => ?_
    have hc : ∀ k : Fin 2, Continuous fun p : Fin 2 → Ainf F => ((ρ w (p k w) : ℝ) : ℂ) := fun k =>
      Complex.continuous_ofReal.comp
        ((hρc w).comp ((continuous_apply w).comp (continuous_apply k)))
    exact (hc 0).add ((hc 1).mul continuous_const)
  have hc2 : Continuous inv := by
    refine continuous_pi fun k => ?_
    revert k
    rw [Fin.forall_fin_two]
    constructor
    · refine continuous_pi fun w => ?_
      exact (hρs w).comp (Complex.continuous_re.comp (continuous_apply w))
    · refine continuous_pi fun w => ?_
      exact (hρs w).comp ((Complex.continuous_im.comp (continuous_apply w)).div_const _)
  exact ⟨⟨⟨fwd, inv, hl, hr⟩, hc1, hc2⟩, fun _ _ => rfl⟩

end

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_equiv (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ Φ : (Ainf F ⊗[F] E) ≃+* (InfinitePlace F → ℂ), IsHomeomorph Φ := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_delta σ h
  obtain ⟨b, hb0, hb1⟩ := exists_basis σ h hδ hδ0
  haveI hTR : IsTotallyReal F := h.1
  choose τ hτ using fun w : InfinitePlace F => exists_tau (E := E) w
  let ρ : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hρc : ∀ w, Continuous (ρ w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hρs : ∀ w, Continuous (ρ w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hρF : ∀ (w : InfinitePlace F) (x : F),
      ((ρ w (algebraMap F (Ainf F) x w) : ℝ) : ℂ) = τ w (algebraMap F E x) := by
    intro w x
    have h1 : τ w (algebraMap F E x) = w.embedding x := DFunLike.congr_fun (hτ w) x
    rw [h1, InfiniteAdeleRing.algebraMap_apply]
    simp only [ρ]
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w _
  let t : InfinitePlace F → ℂ := fun w => τ w δ
  have htre : ∀ w, (t w).re = 0 := by
    intro w
    have h1 : τ w (σ δ) = star (τ w δ) := h.2.2.2 (τ w) δ
    rw [hδ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    simp only [t]
    linarith
  have htim : ∀ w, (t w).im ≠ 0 := by
    intro w h0
    exact hδ0 ((map_eq_zero (τ w)).mp (Complex.ext (htre w) h0))
  let f : Ainf F →+* (InfinitePlace F → ℂ) :=
    Pi.ringHom fun w => (Complex.ofRealHom.comp (ρ w).toRingHom).comp (Pi.evalRingHom _ w)
  let g : E →+* (InfinitePlace F → ℂ) := Pi.ringHom τ
  letI alg : Algebra F (InfinitePlace F → ℂ) := (g.comp (algebraMap F E)).toAlgebra
  let fA : Ainf F →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := f
      commutes' := fun x => funext fun w => hρF w x }
  let gA : E →ₐ[F] (InfinitePlace F → ℂ) :=
    { toRingHom := g
      commutes' := fun _ => rfl }
  let Φ₀ : Ainf F ⊗[F] E →ₐ[F] (InfinitePlace F → ℂ) := Algebra.TensorProduct.productMap fA gA
  obtain ⟨Ψ, hΨ⟩ := exists_psi ρ hρc hρs t htre htim
  let C : (Ainf F ⊗[F] E) ≃ₜ (Fin 2 → Ainf F) := TopK.coordHomeo (Ainf F) b
  have hC : ∀ x k, C x k = (Algebra.TensorProduct.basis (Ainf F) b).repr x k := fun _ _ => rfl
  have hform : ∀ a c : Ainf F, Φ₀ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
      fun w => ((ρ w (a w) : ℝ) : ℂ) + ((ρ w (c w) : ℝ) : ℂ) * t w := by
    intro a c
    funext w
    rw [map_add]
    simp only [Φ₀, Algebra.TensorProduct.productMap_apply_tmul]
    show ((ρ w (a w) : ℝ) : ℂ) * τ w 1 + ((ρ w (c w) : ℝ) : ℂ) * τ w δ = _
    rw [map_one, mul_one]
  have hΦ : ⇑Φ₀ = Ψ ∘ C := by
    funext x
    have hx : x = (C x 0) ⊗ₜ[F] (1 : E) + (C x 1) ⊗ₜ[F] δ := by
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Ainf F) b).sum_repr x]
      rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb0, hb1,
        hC, hC, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    calc Φ₀ x = Φ₀ ((C x 0) ⊗ₜ[F] (1 : E) + (C x 1) ⊗ₜ[F] δ) := congrArg Φ₀ hx
      _ = Ψ (C x) := (hform _ _).trans (funext fun w => (hΨ (C x) w).symm)
  have hhom : IsHomeomorph Φ₀ := by
    rw [hΦ]
    exact (C.trans Ψ).isHomeomorph
  exact ⟨RingEquiv.ofBijective (Φ₀ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ)) hhom.bijective, hhom⟩

end

theorem unimodular_mod_units_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → Ainf F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Ainf F ⊗[F] E, (∃ z : Fin M → Ainf F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Ainf F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Ainf F ⊗[F] E), (a : Ainf F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Ainf F ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ h M
  obtain ⟨Φ, hΦ⟩ := exists_equiv σ h
  exact reduce_of_equiv Φ hΦ M

end GlobalTheory.CompanionTheory.SW.PrimInf
