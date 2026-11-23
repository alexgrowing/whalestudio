import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma realForm_eq_zero {E : Type} [Field E] [NumberField E] {P : Type} [Fintype P] (g : P → (E →+* ℂ))
    (hg : Function.Injective (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p))))
    (u v : P → ℝ) (h : ∀ x : 𝓞 E, ∑ p, (u p * (g p (x : E)).re + v p * (g p (x : E)).im) = 0) :
    ∀ p, u p = 0 ∧ v p = 0 := by
  classical
  let σ : P ⊕ P → (E →* ℂ) := fun k =>
    (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p)) k).toMonoidHom
  have hσ : Function.Injective σ := by
    intro k l hkl
    apply hg
    ext x
    exact DFunLike.congr_fun hkl x
  have hli : LinearIndependent ℂ (fun k => (σ k : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp σ hσ
  have hE : ∀ x : E, ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hdx x (Finset.mem_singleton_self x))
    have h1 := h w
    have hw' : (w : E) = (d : E) * x := by
      rw [← zsmul_eq_mul, ← hw]
    rw [hw'] at h1
    simp only [map_mul, map_intCast, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, add_zero] at h1
    have h3 : (d : ℝ) * ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
      rw [Finset.mul_sum, ← h1]
      exact Finset.sum_congr rfl fun p _ => by ring
    rcases mul_eq_zero.mp h3 with h2 | h2
    · exact absurd (Int.cast_eq_zero.mp h2) hd
    · exact h2
  let c : P ⊕ P → ℂ := Sum.elim (fun p => ((u p : ℂ) - Complex.I * v p) / 2)
    (fun p => ((u p : ℂ) + Complex.I * v p) / 2)
  have hterm : ∀ p (x : E), ((u p : ℂ) - Complex.I * v p) / 2 * g p x +
      ((u p : ℂ) + Complex.I * v p) / 2 * ComplexEmbedding.conjugate (g p) x =
      ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) := by
    intro p x
    rw [ComplexEmbedding.conjugate_coe_eq]
    apply Complex.ext <;> simp <;> ring
  have hsum : ∑ k, c k • (σ k : E → ℂ) = 0 := by
    funext x
    rw [Finset.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    calc _ = ∑ p, ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun p _ => hterm p x
      _ = 0 := by rw [← Complex.ofReal_sum, hE x, Complex.ofReal_zero]
  have hc := (Fintype.linearIndependent_iff.mp hli) c hsum
  intro p
  have h1 : ((u p : ℂ) - Complex.I * v p) / 2 = 0 := hc (Sum.inl p)
  have h1' : (u p : ℂ) - Complex.I * v p = 0 := by
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · norm_num at h
  constructor
  · have h4 := congrArg Complex.re h1'
    simpa using h4
  · have h4 := congrArg Complex.im h1'
    simpa using h4

theorem UpperTheory.Gal.W2.Seed.pRealIso :
    TraceType → RealIso := by
  intro hT E _ _ _ A n
  classical
  obtain ⟨-, -, hpl, him⟩ := hT E A
  have hcardPhi : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) := by
    refine Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1) ⟨?_, ?_⟩)
    · intro a b hab
      exact (hpl (InfinitePlace.mk a.1)).unique rfl hab.symm
    · intro v
      obtain ⟨τ, hτ, -⟩ := hpl v
      exact ⟨τ, hτ⟩
  have hrank : 2 * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E] at h1
    omega
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let b1 := Algebra.TensorProduct.basis ℝ bZ
  let F : (Fin n → 𝓞 E) →ₗ[ℤ] (Phi A × Fin n → ℂ) :=
    LinearMap.pi (fun p : Phi A × Fin n =>
      ((p.1.1.comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap) ∘ₗ LinearMap.proj p.2)
  let L : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] (Phi A × Fin n → ℂ) := b1.constr ℝ (fun k => F (bZ k))
  have hL : ∀ x, L (1 ⊗ₜ x) = F x := by
    have hcomp : (L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1 = F := by
      refine bZ.ext fun k => ?_
      have hk : ((L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1) (bZ k) =
          L (b1 k) := by
        rw [Algebra.TensorProduct.basis_apply]
        rfl
      rw [hk, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun hcomp x
  have dec : ∀ (φ : Module.Dual ℝ (Phi A × Fin n → ℂ)) p (w : ℂ),
      φ (Pi.single p w) = w.re * φ (Pi.single p 1) + w.im * φ (Pi.single p Complex.I) := by
    intro φ p w
    have hw : (Pi.single p w : Phi A × Fin n → ℂ) =
        w.re • (Pi.single p (1 : ℂ) : Phi A × Fin n → ℂ) +
          w.im • (Pi.single p Complex.I : Phi A × Fin n → ℂ) := by
      ext q
      by_cases hq : q = p
      · subst hq
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, hq]
    rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : Function.Injective
      (Sum.elim (fun τ : Phi A => τ.1) (fun τ : Phi A => ComplexEmbedding.conjugate τ.1)) := by
    have hcross : ∀ a b : Phi A, a.1 ≠ ComplexEmbedding.conjugate b.1 := by
      intro a b h
      have h2 := RingHom.congr_fun h (A.ω : E)
      rw [ComplexEmbedding.conjugate_coe_eq, a.2, b.2] at h2
      have h3 := congrArg Complex.im h2
      rw [Complex.conj_im] at h3
      exact him (by linarith)
    rintro (a | a) (b | b) h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd h (hcross a b)
    · exact absurd h.symm (hcross b a)
    · simp only [Sum.elim_inr] at h
      have h' : (a.1 : E →+* ℂ) = b.1 := by
        ext x
        have hx := RingHom.congr_fun h x
        rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq] at hx
        simpa using congrArg (starRingEnd ℂ) hx
      exact congrArg _ (Subtype.ext h')
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hvan : ∀ y, φ (L y) = 0 := by
      intro y
      have hm : φ (L y) ∈ (LinearMap.range L).map φ := ⟨L y, ⟨y, rfl⟩, rfl⟩
      rw [hφ] at hm
      exact (Submodule.mem_bot ℝ).mp hm
    have huv : ∀ i : Fin n, ∀ τ : Phi A,
        φ (Pi.single (τ, i) 1) = 0 ∧ φ (Pi.single (τ, i) Complex.I) = 0 := by
      intro i
      refine realForm_eq_zero (fun τ : Phi A => τ.1) hg _ _ fun x => ?_
      have h1 := hvan (1 ⊗ₜ Pi.single i x)
      rw [hL] at h1
      have hFx : F (Pi.single i x) = ∑ τ : Phi A, Pi.single (τ, i) (τ.1 (x : E)) := by
        ext ⟨τ', i'⟩
        rw [Finset.sum_apply]
        by_cases hi : i' = i
        · subst hi
          rw [Finset.sum_eq_single τ']
          · simp [F]
          · intro τ _ hτ
            simp [Pi.single_apply, hτ]
          · simp
        · simp [F, Pi.single_apply, hi]
      rw [hFx, map_sum] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun τ _ => by rw [dec φ (τ, i) (τ.1 (x : E))]; ring
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.zero_apply, ← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨τ, i⟩ := p
    rw [dec, (huv i τ).1, (huv i τ).2]
    simp
  have hdim : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin n → 𝓞 E)) =
      Module.finrank ℝ (Phi A × Fin n → ℂ) := by
    rw [Module.finrank_eq_card_basis b1,
      Module.finrank_eq_card_basis (Pi.basis fun _ : Phi A × Fin n => Complex.basisOneI)]
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_fin, Fintype.card_prod]
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, ← hrank, hcardPhi]
    ring
  refine ⟨LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩, ?_⟩
  intro x τ i
  show L (1 ⊗ₜ x) (τ, i) = _
  rw [hL]
  rfl
