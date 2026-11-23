import Mathlib

open MvPolynomial Cardinal

namespace GlobalTheory.GaloisDescent

open MvPolynomial Cardinal in

theorem _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis {F F' L L' ι κ : Type*} [Field F] [Field F']
    [Field L] [Field L'] [Algebra F L] [Algebra F' L'] [IsAlgClosed L] [IsAlgClosed L']
    {v : ι → L} {w : κ → L'} (hv : IsTranscendenceBasis F v) (hw : IsTranscendenceBasis F' w)
    (e : MvPolynomial ι F ≃+* MvPolynomial κ F') :
    ∃ σ : L ≃+* L', ∀ p, σ (aeval v p) = aeval w (e p) := by
  letI : Algebra (MvPolynomial ι F) L := (aeval v).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial κ F') L' := (aeval w).toRingHom.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial ι F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hv.1
  have : Module.IsTorsionFree (MvPolynomial κ F') L' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hw.1
  have : IsAlgClosure (MvPolynomial ι F) L := by
    refine ⟨inferInstance, ?_⟩
    have := hv.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hv.1.aevalEquiv.symm (RingHom.id L)
      hv.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval v (hv.1.aevalEquiv.symm a) = algebraMap _ L a
    rw [← hv.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have : IsAlgClosure (MvPolynomial κ F') L' := by
    refine ⟨inferInstance, ?_⟩
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hw.1.aevalEquiv.symm (RingHom.id L')
      hw.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval w (hw.1.aevalEquiv.symm a) = algebraMap _ L' a
    rw [← hw.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  exact ⟨IsAlgClosure.equivOfEquiv L L' e, fun p => IsAlgClosure.equivOfEquiv_algebraMap L L' e p⟩

theorem exists_ringEquiv_extend {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (τ : F ≃+* F) : ∃ σ : L ≃+* L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs (mapEquiv s τ)
  refine ⟨σ, fun a => ?_⟩
  simpa using hσ (C a)

theorem exists_algEquiv_extend {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F]
    [Algebra F L] [Algebra K L] [IsScalarTower K F L] [IsAlgClosed L]
    (τ : F ≃ₐ[K] F) : ∃ σ : L ≃ₐ[K] L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (L := L) τ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, hσ⟩
  rw [IsScalarTower.algebraMap_apply K F L, hσ]
  congr 1
  exact τ.commutes k

theorem exists_algEquiv_apply_eq_add_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {x : L} (hx : Transcendental K x) : ∃ σ : L ≃ₐ[K] L, σ x = x + 1 := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (aeval fun i => X i + 1) (aeval fun i => X i - 1)
      (by ext i : 1; simp) (by ext i : 1; simp)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, ?_⟩
  · simpa [e] using hσ (C k)
  · simpa [e] using hσ (X ⟨x, hxs rfl⟩)

open MvPolynomial Cardinal in

theorem _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_cases halg : IsAlgebraic K x
  · have hxA : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.2 halg
    have hfix : ∀ f : Gal(algebraicClosure K L/K), f ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
      intro f
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (algebraicClosure K L) L
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs
        (MvPolynomial.mapEquiv s (f : algebraicClosure K L ≃+* algebraicClosure K L))
      have hτA : ∀ a : algebraicClosure K L, τ (a : L) = (f a : L) := fun a => by
        simpa using hτ (MvPolynomial.C a)
      let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by
        simpa using hτA (algebraMap K (algebraicClosure K L) k))
      apply Subtype.ext
      rw [← hτA]
      exact hx σ
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact ⟨k, congrArg Subtype.val hk⟩
  · classical
    have hind : AlgebraicIndepOn K id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set L))).2 halg
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    let i : t := ⟨x, hxt rfl⟩
    let φ : MvPolynomial t K ≃ₐ[K] MvPolynomial t K := AlgEquiv.ofAlgHom
      (aeval fun j => if j = i then X j + 1 else X j) (aeval fun j => if j = i then X j - 1 else X j)
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis ht ht φ.toRingEquiv
    have hτx : τ x = x + 1 := by simpa [φ, i] using hτ (X i)
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by simpa [φ] using hτ (C k))
    have h1 := hx σ
    have h2 : τ x = x := h1
    rw [hτx] at h2
    simp at h2

open MvPolynomial Cardinal in

theorem _root_.GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  exact _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x hx

open MvPolynomial Cardinal in

theorem _root_.GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq {K : Type} [Field K] [Countable K] (f g : K →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a, σ (f a) = g a := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  letI Af : Algebra K ℂ := f.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hK hC
  letI Ag : Algebra K ℂ := g.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK hC
  obtain ⟨eqv⟩ := Cardinal.eq.1 (hsc.symm.trans htc)
  obtain ⟨σ, hσ⟩ := @_root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis K K ℂ ℂ s t _ _ _ _ Af Ag _ _ _ _
    hs ht (MvPolynomial.renameEquiv K eqv).toRingEquiv
  refine ⟨σ, fun a => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hσ (MvPolynomial.C a)

end GlobalTheory.GaloisDescent
