import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

private theorem circle_pow_surj' {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by
  intro z
  refine ⟨Circle.exp (Complex.arg z / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  change Circle.exp (Complex.arg z / n) ^ n = z
  rw [← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn', Circle.exp_arg]

theorem circle_extend' {M N : Type} [CommGroup M] [CommGroup N] (f : M →* N)
    (hf : Function.Injective f) (g : M →* Circle) : ∃ h : N →* Circle, ∀ x, h (f x) = g x := by
  let _ : DivisibleBy (Additive Circle) ℤ :=
    divisibleByOfSMulRightSurj (Additive Circle) ℤ (fun hn => circle_pow_surj' hn)
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive f) hf (MonoidHom.toAdditive g)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact DFunLike.congr_fun hh (Additive.ofMul x)

theorem host_star_emb (D : D7) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (@star D.host.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
      (@StarRing.toStarMul _ _ D.host.cmStar))) x) = (starRingEnd ℂ) (φ x) := by
  haveI := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x

private theorem prod_emb_eq_one {R : Ranks} (H : Formalism.BasicNotions.Host R) [Fintype R.Psi] (x : H.E)
    (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : ∏ τ : R.Psi, H.emb (τ : R.GG) x = 1 := by
  classical
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  have h := Algebra.norm_eq_prod_automorphisms H.K x
  rw [H.der.norm_mu x hx, map_one] at h
  have h2 := congrArg H.φ₀ h
  rw [map_one, map_prod] at h2
  rw [h2]
  symm
  have hmem : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ : H.E ≃ₐ[H.K] H.E => (⟨H.gal (σ.restrictScalars ℚ), hmem σ⟩ : R.Psi))
    ⟨fun σ τ hst => ?_, fun g => ?_⟩ _ _ fun σ => ?_
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val hst))
  · have hfix : H.gal.symm g.1 H.sqd = H.sqd :=
      (H.galE_mem_Psi_iff _).1 (by
        show H.gal (H.gal.symm g.1) ∈ _
        rw [MulEquiv.apply_symm_apply]; exact g.2)
    have hK : ∀ y : H.K, H.gal.symm g.1 (y : H.E) = y := by
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.gal.symm g.1)) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        exact (Subgroup.zpowers_le.2
          (show H.gal.symm g.1 ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd from hfix)) hf
      intro y
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle y.2) _ (Subgroup.mem_zpowers _)
    refine ⟨AlgEquiv.ofRingEquiv (f := (H.gal.symm g.1).toRingEquiv) hK, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply g.1
  · show H.φ₀ (σ x) = H.φ₀ (H.gal.symm (H.gal (σ.restrictScalars ℚ)) x)
    rw [MulEquiv.symm_apply_apply]
    rfl

open Classical in
theorem character_linkage_holds : LinkChi := by
  intro D _
  letI := D.host.cmStar

  have hnorm : ∀ (φ : D.host.E →+* ℂ) (z : unitary D.host.E), ‖φ (z : D.host.E)‖ = 1 := by
    intro φ z
    have h1 : φ (star (z : D.host.E)) * φ (z : D.host.E) = 1 := by
      rw [← map_mul, z.2.1, map_one]
    rw [host_star_emb D φ] at h1
    have h2 : ((Complex.normSq (φ (z : D.host.E)) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact h1
    have h3 : Complex.normSq (φ (z : D.host.E)) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have := norm_nonneg (φ (z : D.host.E))
    nlinarith

  let s : unitary D.host.E →* Submodule (𝓞 D.host.E) D.host.E :=
    { toFun := fun z => Submodule.span (𝓞 D.host.E) {(z : D.host.E)}
      map_one' := by
        change Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} = 1
        rw [Submodule.one_eq_span]
      map_mul' := fun a b => by
        change Submodule.span (𝓞 D.host.E) {(a : D.host.E) * (b : D.host.E)} =
          Submodule.span (𝓞 D.host.E) {(a : D.host.E)} * Submodule.span (𝓞 D.host.E) {(b : D.host.E)}
        rw [Submodule.span_mul_span, Set.singleton_mul_singleton] }
  let ι : unitary D.host.E →* (Submodule (𝓞 D.host.E) D.host.E)ˣ := s.toHomUnits

  have hK : ∀ z : unitary D.host.E, ι z = 1 → ∃ m : ℕ, 0 < m ∧ (z : D.host.E) ^ m = 1 := by
    intro z hz
    have hs : Submodule.span (𝓞 D.host.E) {(z : D.host.E)} = 1 := by
      have := congrArg Units.val hz
      simpa [ι, s] using this
    have hmem : (z : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      rw [← hs]; exact Submodule.subset_span rfl
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hmem
    have hint : IsIntegral ℤ (z : D.host.E) := by
      rw [← hy]; exact RingOfIntegers.isIntegral_coe y
    obtain ⟨m, hm, hzm⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one D.host.E ℂ hint
      (fun φ => hnorm φ z)
    exact ⟨m, hm, hzm⟩

  let n : unitary D.host.E →* Circle :=
    { toFun := fun z => ⟨∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹, by
        change _ ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_prod]
        exact Finset.prod_eq_one fun τ _ => by rw [norm_inv, hnorm _ z, inv_one]⟩
      map_one' := by
        apply Circle.ext
        simp
      map_mul' := fun a b => by
        apply Circle.ext
        change (∏ τ : D.what₂.Tau, (embT D τ ((a * b : unitary D.host.E) : D.host.E))⁻¹) =
          (∏ τ : D.what₂.Tau, (embT D τ (a : D.host.E))⁻¹) * ∏ τ : D.what₂.Tau, (embT D τ (b : D.host.E))⁻¹
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun τ _ => ?_
        rw [Submonoid.coe_mul, map_mul, mul_inv] }
  have hn : ∀ z : unitary D.host.E, ((n z : Circle) : ℂ) = ∏ τ : D.what₂.Tau, (embT D τ (z : D.host.E))⁻¹ :=
    fun z => rfl
  have hker : ι.ker ≤ n.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    apply Circle.ext
    rw [hn]
    letI : Fintype D.R.Psi := Fintype.ofEquiv _ D.eTau
    rw [Finset.prod_inv_distrib, Circle.coe_one, inv_eq_one,
      ← prod_emb_eq_one D.host (z : D.host.E) (hK z hz)]
    exact Fintype.prod_equiv D.eTau _ _ fun τ => rfl
  obtain ⟨h, hh⟩ := circle_extend' (QuotientGroup.kerLift ι) (QuotientGroup.kerLift_injective ι)
    (QuotientGroup.lift ι.ker n hker)
  refine ⟨fun 𝔞 => if hu : IsUnit 𝔞 then ((h hu.unit : Circle) : ℂ) else 0, ?_, ?_⟩
  · intro 𝔞 𝔟 ha hb
    obtain ⟨𝔞', -, ha'⟩ := ha
    obtain ⟨𝔟', -, hb'⟩ := hb
    have hua : IsUnit 𝔞 := isUnit_iff_exists_inv.2 ⟨_, ha'⟩
    have hub : IsUnit 𝔟 := isUnit_iff_exists_inv.2 ⟨_, hb'⟩
    have hu : IsUnit (𝔞 * 𝔟) := hua.mul hub
    have hunit : hu.unit = hua.unit * hub.unit := Units.ext rfl
    simp only [dif_pos hu, dif_pos hua, dif_pos hub, hunit, map_mul, Circle.coe_mul]
  · intro z
    have hu : IsUnit (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) := (ι z).isUnit
    have hunit : hu.unit = ι z := Units.ext rfl
    simp only [dif_pos hu, hunit]
    have := hh (QuotientGroup.mk z)
    rw [QuotientGroup.kerLift_mk, QuotientGroup.lift_mk] at this
    rw [this, hn]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
