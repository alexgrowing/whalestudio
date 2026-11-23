import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

private theorem UpperTheory.V.Kum.compact_union (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) (hN : N ≠ 0) (H : ValuationSubring Ω → Set (G F Ω)) (hcl : ∀ A, IsClosed (H A))
    (hconj : ∀ (A : ValuationSubring Ω) (g σ : G F Ω), σ ∈ H (g • A) → g⁻¹ * σ * g ∈ H A) :
    IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ H A} := by
  obtain ⟨-, h2, h3, h4⟩ := placeDict F Ω
  have hfin : (Above F N).Finite := by
    have h0 : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
      simpa using hN
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let T : ValuationSubring Ω → Set (G F Ω) := fun A =>
    (fun p : G F Ω × G F Ω => p.1 * p.2 * p.1⁻¹) '' (Set.univ ×ˢ H A)
  have hT : ∀ A, IsCompact (T A) := fun A =>
    (isCompact_univ.prod (hcl A).isCompact).image (by fun_prop)
  classical
  let P : HeightOneSpectrum (𝓞 F) → Set (G F Ω) := fun v =>
    if h : ∃ A : ValuationSubring Ω, IsPlaceOver A v then T h.choose else ∅
  have hP : ∀ v, IsCompact (P v) := fun v => by
    simp only [P]
    split_ifs
    exacts [hT _, isCompact_empty]
  have e : {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ H A} = ⋃ v ∈ Above F N, P v := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨A, hA, hσ⟩
      obtain ⟨v, hv⟩ := h2 A (h3 A N hN hA)
      refine ⟨v, (h4 A v N hv).1 hA, ?_⟩
      have h : ∃ A : ValuationSubring Ω, IsPlaceOver A v := ⟨A, hv⟩
      simp only [P, dif_pos h]
      obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) h.choose_spec hv
      refine ⟨(g, g⁻¹ * σ * g), ⟨trivial, hconj _ g σ (hg ▸ hσ)⟩, ?_⟩
      simp [mul_assoc]
    · rintro ⟨v, hv, hσ⟩
      simp only [P] at hσ
      split_ifs at hσ with h
      · obtain ⟨⟨g, τ⟩, ⟨-, hτ⟩, rfl⟩ := hσ
        refine ⟨g • h.choose, ?_, ?_⟩
        · rw [GlobalTheory.Cut.ShaBound.valuation_smul_lt_one_iff, map_natCast]
          exact (h4 _ v N h.choose_spec).2 hv
        · have := hconj (g • h.choose) g⁻¹ τ (by rw [inv_smul_smul]; exact hτ)
          rwa [inv_inv] at this
      · exact hσ.elim
  rw [e]
  exact hfin.isCompact_biUnion fun v _ => hP v

theorem UpperTheory.V.Kum.decCompact :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ), N ≠ 0 → IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec (F := F) A} ∧ IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Ine (F := F) A} := by
  intro F Ω _ _ _ _ _ N hN
  exact ⟨compact_union F Ω N hN (fun A => (Dec (F := F) A : Set (G F Ω))) (fun A => isClosed_Dec A)
      fun A g σ h => GlobalTheory.Cut.ShaBound.conj_mem_Dec h,
    compact_union F Ω N hN (fun A => (Ine (F := F) A : Set (G F Ω))) (fun A => isClosed_Ine A)
      fun A g σ h => GlobalTheory.Cut.ShaBound.conj_mem_Ine' h⟩
