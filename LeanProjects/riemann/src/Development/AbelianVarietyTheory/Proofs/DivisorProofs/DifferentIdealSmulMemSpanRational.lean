import Mathlib
open NumberField

namespace GlobalTheory

theorem exists_trace_dual_system (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (m : ℕ) (ω : Fin m → 𝓞 L) (η : Fin m → L),
      (∀ i, η i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ t : L, t = ∑ i, algebraMap K L (Algebra.trace K L (η i * t)) * (ω i : L) := by
  haveI : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) (𝓞 L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) L :=
    IsIntegralClosure.isLocalization (𝓞 K) K L (𝓞 L)
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K _
  let f : Fin m → Module.Dual K L := fun i =>
    hbc.lift ((Algebra.linearMap (𝓞 K) K) ∘ₗ (LinearMap.proj i) ∘ₗ G)
  have hf : ∀ i (a : 𝓞 L), f i (a : L) = algebraMap (𝓞 K) K (G a i) := fun i a =>
    hbc.lift_eq _ a
  let η : Fin m → L := fun i =>
    ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm (f i)
  have hη : ∀ i t, Algebra.trace K L (η i * t) = f i t := fun i t =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate K L) (f i) t
  refine ⟨m, fun i => F (Pi.single i 1), η, fun i => ?_, fun t => ?_⟩
  · rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨G b i, ?_⟩
    rw [Algebra.traceForm_apply, hη]
    exact (hf i b).symm
  · simp_rw [hη]
    have h := hbc.algHom_ext (LinearMap.id : L →ₗ[K] L)
      (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (fun a => by
        have ha : a = ∑ i, G a i • F (Pi.single i 1) := by
          have h1 : a = F (G a) := (LinearMap.congr_fun hFG a).symm
          conv_lhs => rw [h1, LinearMap.pi_apply_eq_sum_univ]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 2
          ext j
          simp [Pi.single_apply, eq_comm]
        change (a : L) = (∑ i, (f i).smulRight ((F (Pi.single i 1) : 𝓞 L) : L)) (a : L)
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hf, algebraMap_smul]
        conv_lhs => rw [ha]
        change algebraMap (𝓞 L) L _ = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap.map_smul _ _)
    have h2 := LinearMap.congr_fun h t
    simpa [LinearMap.sum_apply, Algebra.smul_def] using h2

open NumberField in
private theorem exists_integral_traceDual_expansion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ (N : ℕ) (e : Fin N → 𝓞 L) (c : Fin N → L),
      (∀ k, c k ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ y : L, y = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) • c k := by
  classical
  obtain ⟨N, F, hF⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  have : Module.FinitePresentation (𝓞 K) (𝓞 L) := Module.finitePresentation_of_finite _ _
  have hP : Module.Projective (𝓞 K) (𝓞 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨h, hh⟩ := Module.projective_lifting_property F LinearMap.id hF
  obtain ⟨e, hdec⟩ : ∃ e : Fin N → 𝓞 L, ∀ b : 𝓞 L, b = ∑ k, h b k • e k := by
    refine ⟨fun k => F (Pi.single k 1), fun b => ?_⟩
    have hb := LinearMap.congr_fun hh b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb
    conv_lhs => rw [← hb, ← Finset.univ_sum_single (h b)]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single k (h b k) : Fin N → 𝓞 K) = h b k • Pi.single k 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul]
  let φ : Fin N → (𝓞 L →ₗ[𝓞 K] 𝓞 K) := fun k => LinearMap.proj k ∘ₗ h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin N → Module.Dual K L,
      ∀ k (b : 𝓞 L), ψ k (algebraMap (𝓞 L) L b) = algebraMap (𝓞 K) K (h b k) :=
    ⟨fun k => IsLocalizedModule.mapExtendScalars (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K) K
      (φ k), fun k b => IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
      (IsScalarTower.toAlgHom (𝓞 K) (𝓞 L) L).toLinearMap (Algebra.linearMap (𝓞 K) K)
      (φ k) b⟩
  have hB := traceForm_nondegenerate K L
  obtain ⟨c, hc⟩ : ∃ c : Fin N → L, ∀ k y, Algebra.trace K L (c k * y) = ψ k y :=
    ⟨fun k => ((Algebra.traceForm K L).toDual hB).symm (ψ k), fun k y => by
      rw [← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _⟩
  clear hh hF F this hP
  have hexpO : ∀ b : 𝓞 L,
      algebraMap (𝓞 L) L b = ∑ k, ψ k (algebraMap (𝓞 L) L b) • algebraMap (𝓞 L) L (e k) := by
    intro b
    conv_lhs => rw [hdec b]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.smul_def]
  have hexp : ∀ y : L, y = ∑ k, ψ k y • algebraMap (𝓞 L) L (e k) := by
    intro y
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 L) (nonZeroDivisors (𝓞 K))) y
    obtain ⟨a, ha, has⟩ := s.2
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
    have hy : y = (algebraMap (𝓞 K) K a)⁻¹ • algebraMap (𝓞 L) L b := by
      rw [← hbs, ← has, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
        IsScalarTower.algebraMap_apply (𝓞 K) K L, mul_comm, ← Algebra.smul_def, smul_smul,
        inv_mul_cancel₀ ha0, one_smul]
    clear hbs has
    rw [hy]
    conv_lhs => rw [hexpO b]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_assoc]
  refine ⟨N, e, c, fun k => ?_, fun y => ?_⟩
  · rw [Submodule.mem_traceDual]
    rintro _ ⟨b, rfl⟩
    rw [Algebra.traceForm_apply]
    exact ⟨h b k, by simpa [hψ, Algebra.smul_def, mul_comm] using (hc k (algebraMap (𝓞 L) L b)).symm⟩
  · rw [← sub_eq_zero]
    refine hB.1 _ fun u => ?_
    have h1 : Algebra.trace K L (y * u) = ∑ k, Algebra.trace K L (algebraMap (𝓞 L) L (e k) * y) *
        Algebra.trace K L (c k * u) := by
      conv_lhs => rw [hexp u]
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm y]; ring
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, Algebra.traceForm_apply, smul_eq_mul, h1]
    rw [sub_eq_zero]

open NumberField in

theorem _root_.GlobalTheory.differentIdeal_smul_mem_span_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ) (M : Submodule (𝓞 L) (Fin n → L)), (∀ (σ : L ≃ₐ[K] L), ∀ x ∈ M, (fun i => σ (x i)) ∈ M) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∀ x ∈ M, d • x ∈ Submodule.span (𝓞 L) {y : Fin n → L | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K L (y0 i)} := by
  intro K L _ _ _ _ _ _ n M hM d hd x hx
  classical
  obtain ⟨N, e, c, hcD, hswap⟩ := exists_integral_traceDual_expansion K L
  have hdL : algebraMap (𝓞 L) L d ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
    rw [← coeSubmodule_differentIdeal (𝓞 K) K (𝓞 L)]
    exact (IsLocalization.mem_coeSubmodule _ _).mpr ⟨d, hd, rfl⟩
  have hdc : ∀ k, ∃ r : 𝓞 L, algebraMap (𝓞 L) L r = algebraMap (𝓞 L) L d * c k := fun k =>
    Submodule.mem_one.mp (Submodule.mem_div_iff_forall_mul_mem.mp hdL _ (hcD k))
  choose r hr using hdc
  set t : Fin N → Fin n → L :=
    fun k i => algebraMap K L (Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i)) with ht
  have htM : ∀ k, t k ∈ M := by
    intro k
    have : t k = ∑ σ : L ≃ₐ[K] L, fun i => σ ((e k • x) i) := by
      funext i
      simp only [ht, Finset.sum_apply, Pi.smul_apply, trace_eq_sum_automorphisms, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun σ _ => hM σ _ (M.smul_mem _ hx)
  have hdx : d • x = ∑ k, r k • t k := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ht, Algebra.smul_def, hr]
    conv_lhs => rw [hswap (x i)]
    simp only [Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨htM k, fun i => Algebra.trace K L (algebraMap (𝓞 L) L (e k) * x i), rfl⟩)

end GlobalTheory
