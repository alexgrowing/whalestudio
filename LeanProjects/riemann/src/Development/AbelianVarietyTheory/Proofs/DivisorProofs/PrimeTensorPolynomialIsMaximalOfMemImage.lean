import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC
open GlobalTheory.EtC

namespace GlobalTheory.ClosedFibre
open Polynomial
open scoped TensorProduct

theorem mem_range_of_eval₂ {K D : Type} [Field K] [IsAlgClosed K] [CommRing D] [IsDomain D]
    (ψ : K →+* D) (f : K[X]) (hf : f ≠ 0) (τ : D) (h : f.eval₂ ψ τ = 0) : ∃ r, ψ r = τ := by
  letI : Algebra K D := ψ.toAlgebra
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (natDegree_pos_iff_degree_pos.mp hd).ne'
  have hm : (f * C f.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hf
  exact GlobalTheory.AICIff.root_mem_range hK _ _ hm rfl τ (by
    rw [aeval_def, eval₂_mul]
    change eval₂ ψ τ f * _ = 0
    rw [h, zero_mul])

theorem mem_range_of_etale {R K E D : Type} [CommRing R] [Field K] [IsAlgClosed K] [CommRing E]
    [CommRing D] [IsDomain D] [Algebra R K] [Algebra R E] [Algebra.Etale R E] [Algebra R D]
    (ψ : K →ₐ[R] D) (Φ : E →ₐ[R] D) (u : E) : ∃ r, ψ r = Φ u := by
  haveI : Algebra.Etale K (K ⊗[R] E) := Algebra.Etale.baseChange R E K
  haveI : Module.Finite K (K ⊗[R] E) := Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral K (K ⊗[R] E) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := K) ((1 : K) ⊗ₜ[R] u)
  let Θ : K ⊗[R] E →ₐ[R] D := Algebra.TensorProduct.productMap ψ Φ
  have hΘ : (Θ : K ⊗[R] E →+* D).comp (algebraMap K (K ⊗[R] E)) = (ψ : K →+* D) := by
    ext k
    simp [Θ, Algebra.TensorProduct.algebraMap_apply]
  refine mem_range_of_eval₂ (ψ : K →+* D) f hfm.ne_zero (Φ u) ?_
  have h2 := congrArg (Θ : K ⊗[R] E →+* D) hf
  rw [hom_eval₂, hΘ, map_zero] at h2
  simpa [Θ] using h2

end GlobalTheory.ClosedFibre

namespace GlobalTheory.ClosedFibre
open Polynomial

theorem isMaximal_of_mem : ∀ (T : Type) [CommRing T] [IsDomain T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → ∀ g : Polynomial T, g ≠ 0 → algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P → P.IsMaximal ∧ ∀ x : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ∃ c d : T, d ≠ 0 ∧ algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) d * x - algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) c ∈ P := by
  intro T _ _ hT O _ _ _ _ hO P hP g hg hgP
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let K := FractionRing T
  haveI : IsAlgClosed K := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := hP
  let mk : L →+* L ⧸ P := Ideal.Quotient.mk P
  have hunitL : ∀ t : T, t ≠ 0 → IsUnit (algebraMap T L t) := by
    intro t ht
    have := IsLocalization.map_units L (⟨algebraMap T O t, ⟨t, mem_nonZeroDivisors_of_ne_zero ht, rfl⟩⟩ :
      Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    rwa [IsScalarTower.algebraMap_apply T O L]
  have hunit : ∀ y : nonZeroDivisors T, IsUnit ((mk.comp (algebraMap T L)) y) :=
    fun y => (hunitL y (nonZeroDivisors.ne_zero y.2)).map mk
  let ψ : K →+* L ⧸ P := IsLocalization.lift (M := nonZeroDivisors T) (S := K) hunit
  have hψ : ψ.comp (algebraMap T K) = mk.comp (algebraMap T L) := IsLocalization.lift_comp hunit
  let τ : L ⧸ P := mk (algebraMap (Polynomial T) L X)
  have hpoly : mk.comp (algebraMap (Polynomial T) L) = eval₂RingHom (mk.comp (algebraMap T L)) τ := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rw [IsScalarTower.algebraMap_apply T (Polynomial T) L, Polynomial.algebraMap_apply]
      rfl
    · simp [τ]
  obtain ⟨a, ha⟩ : ∃ a, ψ a = τ := by
    refine mem_range_of_eval₂ ψ (g.map (algebraMap T K))
      ((Polynomial.map_ne_zero_iff (IsFractionRing.injective T K)).2 hg) τ ?_
    rw [eval₂_map, hψ, ← coe_eval₂RingHom, ← hpoly, RingHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgP
  letI : Algebra (Polynomial T) K := (eval₂RingHom (algebraMap T K) a).toAlgebra
  let ψA : K →ₐ[Polynomial T] L ⧸ P :=
    { ψ with
      commutes' := fun p => by
        change ψ (eval₂ (algebraMap T K) a p) = mk (algebraMap (Polynomial T) L p)
        rw [hom_eval₂, hψ, ha, ← RingHom.comp_apply mk, hpoly, coe_eval₂RingHom] }
  have key : ∀ o : O, ∃ r, ψ r = mk (algebraMap O L o) := by
    intro o
    obtain ⟨ι, _, _, _, Si, -, hcov, hE⟩ := hO
    obtain ⟨i, hi⟩ := hcov o
    obtain ⟨E, _, _, _, Q, _, ⟨e⟩⟩ := hE i
    let Φ0 : Localization.AtPrime Q →ₐ[Polynomial T] L ⧸ P :=
      (Ideal.Quotient.mkₐ (Polynomial T) P).comp
        ((IsScalarTower.toAlgHom (Polynomial T) O L).comp ((Si i).val.comp e.toAlgHom))
    let Φ : E →ₐ[Polynomial T] L ⧸ P :=
      Φ0.comp (IsScalarTower.toAlgHom (Polynomial T) E (Localization.AtPrime Q))
    obtain ⟨⟨u, s⟩, hus⟩ := IsLocalization.mk'_surjective Q.primeCompl (e.symm ⟨o, hi⟩)
    obtain ⟨r1, h1⟩ := mem_range_of_etale ψA Φ u
    obtain ⟨r2, h2⟩ := mem_range_of_etale ψA Φ s
    have hsu : IsUnit (Φ s) := (IsLocalization.map_units (Localization.AtPrime Q) s).map Φ0
    have ho : Φ0 (e.symm ⟨o, hi⟩) = mk (algebraMap O L o) := by
      change Ideal.Quotient.mk P (algebraMap O L ((e (e.symm ⟨o, hi⟩) : Si i) : O)) = mk (algebraMap O L o)
      rw [AlgEquiv.apply_symm_apply]
    have hmul : Φ0 (e.symm ⟨o, hi⟩) * Φ s = Φ u := by
      rw [← hus]
      simp only [Φ, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [← map_mul, IsLocalization.mk'_spec]
    have h1' : ψA r1 = ψ r1 := rfl
    have h2' : ψA r2 = ψ r2 := rfl
    rw [h1'] at h1
    rw [h2'] at h2
    have hr2 : r2 ≠ 0 := by
      rintro rfl
      rw [map_zero] at h2
      exact hsu.ne_zero h2.symm
    refine ⟨r1 * r2⁻¹, ?_⟩
    have hne : ψ r2 ≠ 0 := h2 ▸ hsu.ne_zero
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hr2, h1, ← ho, h2, hmul]
  have hall : ∀ x : L, ∃ r, ψ r = mk x := by
    intro x
    obtain ⟨⟨o, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
    obtain ⟨t, ht, hts⟩ := s.2
    obtain ⟨r, hr⟩ := key o
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hk : ψ (algebraMap T K t) = mk (algebraMap O L s) := by
      rw [← RingHom.comp_apply ψ, hψ, RingHom.comp_apply, IsScalarTower.algebraMap_apply T O L, ← hts]
    have hne : ψ (algebraMap T K t) ≠ 0 := by
      rw [hk]
      exact ((IsLocalization.map_units L s).map mk).ne_zero
    have hk0 : algebraMap T K t ≠ 0 := fun h => hne (by rw [h, map_zero])
    refine ⟨r * (algebraMap T K t)⁻¹, ?_⟩
    apply mul_right_cancel₀ hne
    rw [← map_mul, inv_mul_cancel_right₀ hk0, hr, hk, ← map_mul, IsLocalization.mk'_spec]
  have hfield : IsField (L ⧸ P) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {y} hy => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hall x
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hy (by rw [← hr, map_zero])
    exact ⟨ψ r⁻¹, by rw [← hr, ← map_mul, mul_inv_cancel₀ hr0, map_one]⟩
  refine ⟨Ideal.Quotient.maximal_of_isField P hfield, fun x => ?_⟩
  obtain ⟨r, hr⟩ := hall x
  obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) r
  refine ⟨c, d, nonZeroDivisors.ne_zero d.2, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
  have h1 : ψ (IsLocalization.mk' K c d) * ψ (algebraMap T K d) = ψ (algebraMap T K c) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hd : ψ (algebraMap T K d) = Ideal.Quotient.mk P (algebraMap T L d) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  have hc : ψ (algebraMap T K c) = Ideal.Quotient.mk P (algebraMap T L c) := by
    rw [← RingHom.comp_apply ψ, hψ]; rfl
  rw [← hd, ← hc, ← h1, ← hr, mul_comm]
  exact sub_self _

end GlobalTheory.ClosedFibre
