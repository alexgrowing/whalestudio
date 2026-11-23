import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOnePrimeIntegralClosureIffDvdIrreduciblStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialRingIrreduciblePrimeReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanDLiftClearDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DadjCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialRelationLocalRingBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorWedgeEqOfLocalizedSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteTypeOfCharZeroStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_top_coeff_iff_pole : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB _ τ hτ Q hQ hQh t s e ht he hsQ hQs hts z
  obtain ⟨a₀, r₀, ha₀, hr₀, hrt⟩ := hts
  have htQ : ∀ b : B, (b : K) = algebraMap F K t → b ∈ Q := by
    intro b hb
    have h1 : r₀ * b = a₀ * s ^ e := Subtype.ext (by push_cast; rw [hb]; exact hrt)
    have h2 : r₀ * b ∈ Q := h1 ▸ Q.mul_mem_left _ (Q.pow_mem_of_mem hsQ e (by omega))
    exact (hQ.mem_or_mem h2).resolve_left hr₀
  have hcomap := GlobalTheory.T.mem_heightOne_prime_integralClosure_iff_dvd_irreducible k F K d u hu A hA B hB Q hQ hQh t ht htQ
  obtain ⟨htp, m, rfl, y, hy⟩ := GlobalTheory.T.polynomial_ring_irreducible_prime_reduction k F d u hu A hA t ht
  have hAft : Algebra.FiniteType k A := by
    subst hA
    classical
    exact (Subalgebra.fg_iff_finiteType _).1 ⟨Finset.univ.image u, by simp⟩
  have ht0 : t ≠ 0 := ht.ne_zero
  have hP : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  have genA := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k F K A (Ideal.span {t}) hP t (Ideal.mem_span_singleton_self t) ht0
    (fun y hy => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨c, 1, (Ideal.ne_top_iff_one _).1 hP.ne_top, by ring⟩) m y hy

  have memB : ∀ a : A, algebraMap F K (a : F) ∈ B := fun a => by
    rw [hB]; exact (Subalgebra.mem_restrictScalars k).2 ((integralClosure A K).algebraMap_mem a)
  let ιB : A → B := fun a => ⟨algebraMap F K (a : F), memB a⟩
  have hιQ : ∀ a : A, ιB a ∈ Q ↔ a ∈ Ideal.span {t} := fun a => by
    rw [Ideal.mem_span_singleton]; exact hcomap a (ιB a) rfl
  set du : DR k K := ExteriorAlgebra.ιMulti K (m + 1) fun j => D k K (algebraMap F K (u j)) with hdu
  have hdu0 : du ≠ 0 := fun h => by rw [h, map_zero] at hτ; exact zero_ne_one hτ
  set gA : Fin (m + 1) → Ω[K⁄k] := Fin.cons (D k K (algebraMap F K (t : F))) (fun j => D k K (algebraMap F K (y j : F))) with hgA
  obtain ⟨rA, hrA, aA, hA1⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) gA (fun j => D k K (algebraMap F K (u j))) (fun i => by
    obtain ⟨r, hr, c, hc⟩ := genA ⟨u i, hA ▸ Algebra.subset_adjoin (Set.mem_range_self i)⟩
    exact ⟨r, hr, c, hc⟩)
  obtain ⟨r', hr', c', hA2⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span A K Ω[K⁄k] (Ideal.span {t}).primeCompl (m + 1) (fun j => D k K (algebraMap F K (u j))) gA (fun i => by
    have key : ∀ v : A, ∃ c : Fin (m + 1) → A, D k K (algebraMap F K (v : F)) = ∑ l, algebraMap A K (c l) • D k K (algebraMap F K (u l)) := by
      intro v
      obtain ⟨c, hc, hc'⟩ := GlobalTheory.T.exists_D_eq_sum_smul_D_of_mem_adjoin k F K (m + 1) u (v : F) (hA ▸ v.2)
      exact ⟨fun j => ⟨c j, hA ▸ hc j⟩, hc'⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨c, hc⟩ := key t
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩
    · obtain ⟨c, hc⟩ := key (y j)
      exact ⟨1, Submonoid.one_mem _, c, by rw [map_one, one_smul]; exact hc⟩)
  have hAeq : rA * r' = aA * c' := by
    apply FaithfulSMul.algebraMap_injective A K
    have h3 : (algebraMap A K (rA * r')) • du = (algebraMap A K (aA * c')) • du := by
      rw [map_mul, map_mul, mul_comm, mul_smul, hA1, smul_comm, hA2, smul_smul, mul_comm]
    exact smul_left_injective K hdu0 h3
  have haA : aA ∉ Ideal.span {t} := fun h => by
    have : rA * r' ∈ Ideal.span {t} := hAeq ▸ Ideal.mul_mem_right _ _ h
    rcases hP.mem_or_mem this with h4 | h4
    · exact hrA h4
    · exact hr' h4

  let y' : Fin m → B := fun j => ιB (y j)
  have hy' := GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' k F K A B hB Q hQ t hcomap m y hy y' (fun j => rfl)
  haveI := GlobalTheory.T.integralClosure_finiteType_over_adjoin k F K (m + 1) u hu A hA B hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h5 : (r₀ : K) * algebraMap F K t = 0 := by rw [hrt]; simp [zero_pow (by omega : e ≠ 0)]
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact hr₀ (by rw [show r₀ = 0 from Subtype.ext h6]; exact Q.zero_mem)
    · exact ht0 (by
        have : (t : F) = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h6
        exact Subtype.ext this)
  have genB := GlobalTheory.T.exists_not_mem_smul_D_eq_sum k K K B Q hQ s hsQ hs0 hQs m y' hy'
  simp only [Algebra.algebraMap_self_apply] at genB
  obtain ⟨N, Dn, hN, hDn, hND⟩ := GlobalTheory.T.differential_relation_local_ring_bound k K B Q hQ s m (fun j => (y' j : K)) (algebraMap F K t) e he hsQ genB ⟨a₀, r₀, ha₀, hr₀, hrt⟩
  set ω : DR k K := ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) with hω
  let Dt : B := Dn * ιB rA
  let Nt : B := N * ιB aA
  have hDt : Dt ∉ Q := fun h => (hQ.mem_or_mem h).elim hDn (fun h' => hrA ((hιQ rA).1 h'))
  have hNt : Nt ∉ Q := fun h => (hQ.mem_or_mem h).elim hN (fun h' => haA ((hιQ aA).1 h'))
  have hmain : (Dt : K) • du = ((Nt : K) * (s : K) ^ (e - 1)) • ω := by
    have h7 : (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) gA = ((N : K) * (s : K) ^ (e - 1)) • ω := hND
    have hA1' : (algebraMap F K (rA : F)) • du = (algebraMap F K (aA : F)) • ExteriorAlgebra.ιMulti K (m + 1) gA := hA1
    show ((Dn : K) * algebraMap F K (rA : F)) • du = ((N : K) * algebraMap F K (aA : F) * (s : K) ^ (e - 1)) • ω
    rw [mul_smul, hA1', smul_comm, h7, smul_smul]
    congr 1
    ring
  have hkey : (Dt : K) = (Nt : K) * (s : K) ^ (e - 1) * τ ω := by
    have := congrArg τ hmain
    rw [map_smul, map_smul, hτ, smul_eq_mul, smul_eq_mul, mul_one] at this
    rw [this]
  have hv0 : (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K)) : Fin (m + 1) → Ω[K⁄k]) = fun j => D k K ((Fin.cons (s : K) (fun j => (y' j : K)) : Fin (m + 1) → K) j) := by
    funext j; exact Fin.cases rfl (fun j => rfl) j
  have hωmem : ∀ b : B, (b : K) • ω ∈ omB k K B (m + 1) := fun b => by
    refine Submodule.subset_span ⟨b, b.2, Fin.cons (s : K) (fun j => (y' j : K)), fun j => Fin.cases s.2 (fun j => (y' j).2) j, ?_⟩
    rw [hω, hv0]
  have P : ∀ yy ∈ omB k K B (m + 1), ∃ c ρ : B, ρ ∉ Q ∧ (ρ : K) * (s : K) ^ (e - 1) * τ yy = c := by
      intro yy hyy
      unfold omB at hyy
      induction hyy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, v, hv, rfl⟩ := hx
        obtain ⟨ρ, hρ, β, hβ⟩ := GlobalTheory.T.exterior_wedge_eq_of_localized_span B K Ω[K⁄k] Q.primeCompl (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y' j : K))) (fun j => D k K (v j)) (fun i => genB ⟨v i, hv i⟩)
        have hβ' : (ρ : K) • ExteriorAlgebra.ιMulti K (m + 1) (fun j => D k K (v j)) = (β : K) • ω := hβ
        have h8 := congrArg τ hβ'
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h8
        refine ⟨⟨b, hb⟩ * β * Dt, ρ * Nt, fun h => (hQ.mem_or_mem h).elim hρ hNt, ?_⟩
        rw [map_smul, smul_eq_mul]
        push_cast
        rw [hkey]
        linear_combination ((b : K) * (Nt : K) * (s : K) ^ (e - 1)) * h8
      | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 hQ.ne_top, by simp⟩
      | add x w _ _ hx hw =>
        obtain ⟨c1, ρ1, h1, e1⟩ := hx
        obtain ⟨c2, ρ2, h2, e2⟩ := hw
        refine ⟨ρ2 * c1 + ρ1 * c2, ρ1 * ρ2, fun h => (hQ.mem_or_mem h).elim h1 h2, ?_⟩
        rw [map_add]; push_cast
        linear_combination (ρ2 : K) * e1 + (ρ1 : K) * e2
      | smul a x _ hx =>
        obtain ⟨c, ρ, h1, e1⟩ := hx
        refine ⟨algebraMap k B a * c, ρ, h1, ?_⟩
        rw [τ.map_smul_of_tower, Algebra.smul_def]
        push_cast
        rw [← e1]
        ring
  constructor
  · rintro ⟨r, hr, yy, hyy, hτy⟩
    obtain ⟨c, ρ, hρ, hc⟩ := P yy hyy
    refine ⟨c, ρ * r, fun h => (hQ.mem_or_mem h).elim hρ hr, ?_⟩
    rw [← hc, hτy]; push_cast; ring
  · rintro ⟨c, r, hr, hc⟩
    refine ⟨Dt * r, fun h => (hQ.mem_or_mem h).elim hDt hr, ((c * Nt : B) : K) • ω, hωmem _, ?_⟩
    rw [map_smul, smul_eq_mul]
    push_cast
    rw [hkey]
    linear_combination (-((Nt : K) * τ ω)) * hc

end GlobalTheory.PD
