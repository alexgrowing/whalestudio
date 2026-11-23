import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ExistsRingEquivExtendOfIsTranscendenceBasis

namespace GroundTheory.Global

open Polynomial IntermediateField

section General

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]

omit [IsAlgClosed Ω] in

theorem IsTranscendenceBasis.extendScalars_of_isAlgebraic {E : Type*} [Field E] [Algebra F E]
    [Algebra E Ω] [IsScalarTower F E Ω] [Algebra.IsAlgebraic F E] {ι : Type*} {v : ι → Ω}
    (hv : IsTranscendenceBasis F v) : IsTranscendenceBasis E v := by
  refine (hv.1.extendScalars E).isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun z => ?_⟩
  have le : Algebra.adjoin F (Set.range v) ≤ (Algebra.adjoin E (Set.range v)).restrictScalars F :=
    Algebra.adjoin_le fun z hz => (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  exact (hv.isAlgebraic.isAlgebraic z).tower_top_of_subalgebra_le le

theorem exists_algEquiv_apply_eq_of_transcendental {x y : Ω} (hx : Transcendental F x)
    (hy : Transcendental F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  classical
  have ind : ∀ z : Ω, Transcendental F z → AlgebraicIndepOn F id ({z} : Set Ω) := fun z hz =>
    (algebraicIndependent_singleton_iff (⟨z, rfl⟩ : ({z} : Set Ω))).mpr hz
  obtain ⟨t₁, hxt, ht₁⟩ := exists_isTranscendenceBasis_superset (ind x hx)
  obtain ⟨t₂, hyt, ht₂⟩ := exists_isTranscendenceBasis_superset (ind y hy)
  have hx₁ : x ∈ t₁ := Set.singleton_subset_iff.mp hxt
  have hy₂ : y ∈ t₂ := Set.singleton_subset_iff.mp hyt
  obtain ⟨f⟩ := Cardinal.eq.1 (ht₁.cardinalMk_eq_trdeg.trans ht₂.cardinalMk_eq_trdeg.symm)
  let φ : t₁ ≃ t₂ := f.trans (Equiv.swap (f ⟨x, hx₁⟩) ⟨y, hy₂⟩)
  obtain ⟨σ, hσF, hσv⟩ :=
    exists_ringEquiv_extend_of_isTranscendenceBasis (RingEquiv.refl F) ht₁ ht₂ φ
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => hσF a, ?_⟩
  have := hσv ⟨x, hx₁⟩
  simp only [φ, Equiv.trans_apply, Equiv.swap_apply_left] at this
  exact this

theorem exists_algEquiv_apply_eq_of_minpoly_eq {x y : Ω} (hx : IsAlgebraic F x)
    (h : minpoly F x = minpoly F y) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  have hy : IsAlgebraic F y := ⟨minpoly F x, minpoly.ne_zero hx.isIntegral, h ▸ minpoly.aeval _ _⟩
  have := isAlgebraic_adjoin_simple hx.isIntegral
  have := isAlgebraic_adjoin_simple hy.isIntegral
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis
    (minpoly.algEquiv hx h).toRingEquiv
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮x⟯) hs)
    (IsTranscendenceBasis.extendScalars_of_isAlgebraic (E := F⟮y⟯) hs) (Equiv.refl s)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => ?_, ?_⟩
  · have h1 := hσ (algebraMap F F⟮x⟯ a)
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes] at h1
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  · have := hσ (AdjoinSimple.gen F x)
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_apply] at this
    simpa using this

theorem mem_bot_iff_forall_algEquiv_apply_eq [PerfectField F] {x : Ω} :
    x ∈ (⊥ : IntermediateField F Ω) ↔ ∀ σ : Ω ≃ₐ[F] Ω, σ x = x := by
  refine ⟨fun hx σ => ?_, fun h => ?_⟩
  · obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact σ.commutes a
  by_contra hx
  by_cases halg : IsAlgebraic F x
  · have hsep : IsSeparable F x :=
      PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)
    have hx' : x ∉ (⊥ : Subalgebra F Ω) := by
      rwa [Algebra.mem_bot, ← IntermediateField.mem_bot]
    obtain ⟨y, hne, hy⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hsep (IsAlgClosed.splits _)).mp hx'
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq halg hy
    exact hne (hσ ▸ h σ).symm
  · have htr : Transcendental F x := halg
    have htr' : Transcendental F (x + 1) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental htr htr'
    have := hσ.symm.trans (h σ)
    simp at this

variable [CharZero Ω]

theorem infinite_range_apply_of_transcendental {x : Ω} (hx : Transcendental ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Infinite := by
  have hx' : Transcendental ℚ (x + 1) := fun h' =>
    hx (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental hx hx'
  have hpow : ∀ n : ℕ, (σ ^ n) x = x + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, hσ, map_natCast]
      push_cast; ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ fun n =>
    ⟨(σ ^ n).toRingEquiv, hpow n⟩
  intro m n hmn
  exact_mod_cast add_left_cancel hmn

omit [IsAlgClosed Ω] in

theorem finite_range_apply_of_isAlgebraic {x : Ω} (hx : IsAlgebraic ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite := by
  refine ((minpoly ℚ x).rootSet_finite Ω).subset ?_
  rintro _ ⟨σ, rfl⟩
  rw [mem_rootSet]
  refine ⟨minpoly.ne_zero hx.isIntegral, ?_⟩
  have := Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toRatAlgHom x (minpoly ℚ x)
  rw [minpoly.aeval, map_zero] at this
  simpa using this

theorem finite_range_apply_iff_isAlgebraic {x : Ω} :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Finite ↔ IsAlgebraic ℚ x :=
  ⟨fun h => by_contra fun hx => infinite_range_apply_of_transcendental hx h,
    finite_range_apply_of_isAlgebraic⟩

end General

theorem Complex.isAlgebraic_of_finite_conjugates {x : ℂ}
    (hx : (Set.range fun σ : ℂ ≃+* ℂ => σ x).Finite) : IsAlgebraic ℚ x :=
  finite_range_apply_iff_isAlgebraic.mp hx

end GroundTheory.Global
