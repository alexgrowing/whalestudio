import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.SW.QuadMaxIdeal

section Quad

variable {R O : Type} [CommRing R] [CommRing O] [IsLocalRing R] (ι : R →+* O) (δ : O) (D : R)

omit [IsLocalRing R] in

theorem isUnit_of_norm (hδ : δ * δ = ι D) (p q : R) (h : IsUnit (p ^ 2 - D * q ^ 2)) :
    IsUnit (ι p + ι q * δ) := by
  obtain ⟨w, hw⟩ := h.exists_right_inv
  refine IsUnit.of_mul_eq_one ((ι p - ι q * δ) * ι w) ?_
  have h1 : ι (p ^ 2 - D * q ^ 2) * ι w = 1 := by rw [← map_mul, hw, map_one]
  simp only [map_sub, map_mul, map_pow] at h1
  linear_combination h1 - (ι q) ^ 2 * ι w * hδ

theorem isUnit_add_mem {u x : R} (hu : IsUnit u) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (u + x) := by
  by_contra h
  have h1 : u + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : u ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ h1 hx
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isUnit_of_not_mem {x : R} (hx : x ∉ IsLocalRing.maximalIdeal R) : IsUnit x := by
  by_contra h
  exact hx ((IsLocalRing.mem_maximalIdeal _).2 h)

theorem map_mem (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    {P : Ideal O} (hP : P.IsMaximal) {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) :
    ι r ∈ P := by
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := hP.exists_inv hn
  obtain ⟨a, b, rfl⟩ := hsp y
  have hi' : i = ι (1 - a * r) + ι (-(b * r)) * δ := by
    simp only [map_sub, map_mul, map_neg, map_one]
    linear_combination e
  have hu : IsUnit ((1 - a * r) ^ 2 - D * (-(b * r)) ^ 2) := by
    have e1 : (1 - a * r) ^ 2 - D * (-(b * r)) ^ 2 =
        1 + r * (a ^ 2 * r - 2 * a - D * b ^ 2 * r) := by ring
    rw [e1]
    exact isUnit_add_mem isUnit_one (Ideal.mul_mem_right _ _ hr)
  have hiu : IsUnit i := by
    rw [hi']
    exact isUnit_of_norm ι δ D hδ _ _ hu
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hi hiu)

theorem eq_span_of_factor (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (s c : R) (π' : O) (hm : IsLocalRing.maximalIdeal R = Ideal.span {c})
    (hfac : (δ - ι s) * π' = ι c) {P : Ideal O} (hP : P.IsMaximal) (hπ : δ - ι s ∈ P) :
    P = Ideal.span {δ - ι s} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 hπ)
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hr : ι (p + q * s) ∈ P := by
    have e : ι (p + q * s) = (ι p + ι q * δ) - ι q * (δ - ι s) := by
      simp only [map_add, map_mul]; ring
    rw [e]
    exact P.sub_mem hy (P.mul_mem_left _ hπ)
  have hm' : p + q * s ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hr ((isUnit_of_not_mem hn).map ι))
  rw [hm, Ideal.mem_span_singleton'] at hm'
  obtain ⟨a, ha⟩ := hm'
  have h1 : ι a * ι c = ι p + ι q * ι s := by
    rw [← map_mul, ha, map_add, map_mul]
  refine Ideal.mem_span_singleton'.2 ⟨ι q + ι a * π', ?_⟩
  linear_combination (ι a) * hfac + h1

theorem eq_span_of_nonsquare (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hsq : ∀ e : R, e ^ 2 - D ∉ IsLocalRing.maximalIdeal R)
    {P : Ideal O} (hP : P.IsMaximal) : P = Ideal.span {ι ϖ} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).2 (map_mem ι δ D hδ hsp hP hϖm))
  intro y hy
  obtain ⟨p, q, rfl⟩ := hsp y
  have hN : p ^ 2 - D * q ^ 2 ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hy
      (isUnit_of_norm ι δ D hδ p q (isUnit_of_not_mem hn)))
  have hq : q ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    obtain ⟨w, hw⟩ := (isUnit_of_not_mem hn).exists_right_inv
    apply hsq (p * w)
    have e : (p * w) ^ 2 - D = w ^ 2 * (p ^ 2 - D * q ^ 2) := by
      linear_combination (D * (q * w + 1)) * hw
    rw [e]
    exact Ideal.mul_mem_left _ _ hN
  have hp : p ∈ IsLocalRing.maximalIdeal R := by
    have h1 : p ^ 2 ∈ IsLocalRing.maximalIdeal R := by
      have e : p ^ 2 = (p ^ 2 - D * q ^ 2) + D * q ^ 2 * 1 := by ring
      rw [e]
      refine Ideal.add_mem _ hN (Ideal.mul_mem_right _ _ ?_)
      exact Ideal.mul_mem_left _ _ (by
        rw [pow_two]; exact Ideal.mul_mem_left _ _ hq)
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem 2 h1
  rw [hϖ, Ideal.mem_span_singleton'] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  refine Ideal.mem_span_singleton'.2 ⟨ι a + ι b * δ, ?_⟩
  simp only [map_mul]
  ring

theorem exists_root (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (e : R)
    (he : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R) :
    ∃ e' : R, IsLocalRing.maximalIdeal R = Ideal.span {e' ^ 2 - D} := by
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have heu : IsUnit e := by
    have h1 : IsUnit (D + (e ^ 2 - D)) := isUnit_add_mem hD he
    have h3 : IsUnit (e ^ 2) := by simpa using h1
    exact (isUnit_pow_iff two_ne_zero).1 h3
  have he' := he
  rw [hϖ, Ideal.mem_span_singleton'] at he'
  obtain ⟨c, hc⟩ := he'
  by_cases hcu : IsUnit c
  · refine ⟨e, ?_⟩
    rw [← hc, Ideal.span_singleton_mul_left_unit hcu, hϖ]
  · have hcm : c ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hcu
    have hu : IsUnit (2 * e + (c + ϖ)) :=
      isUnit_add_mem (h2.mul heu) (Ideal.add_mem _ hcm hϖm)
    refine ⟨e + ϖ, ?_⟩
    have e1 : (e + ϖ) ^ 2 - D = (2 * e + (c + ϖ)) * ϖ := by
      linear_combination -hc
    rw [e1, Ideal.span_singleton_mul_left_unit hu, hϖ]

theorem exists_gens (hδ : δ * δ = ι D) (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) :
    ∃ (π₁ π₂ : O) (c : R), c ≠ 0 ∧ π₁ ∣ ι c ∧ π₂ ∣ ι c ∧
      ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂} := by
  by_cases hsq : ∃ e : R, e ^ 2 - D ∈ IsLocalRing.maximalIdeal R
  · obtain ⟨e0, he0⟩ := hsq
    obtain ⟨e, hm⟩ := exists_root D hD h2 ϖ hϖ e0 he0
    have hc0 : e ^ 2 - D ≠ 0 := by
      intro h0
      have h1 : ϖ ∈ Ideal.span {e ^ 2 - D} := by
        rw [← hm, hϖ]; exact Ideal.mem_span_singleton_self ϖ
      rw [h0] at h1
      exact hϖ0 (by simpa using h1)
    have f1 : (δ - ι e) * (-(δ - ι (-e))) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    have f2 : (δ - ι (-e)) * (-(δ - ι e)) = ι (e ^ 2 - D) := by
      simp only [map_sub, map_neg, map_pow]
      linear_combination -hδ
    refine ⟨δ - ι e, δ - ι (-e), e ^ 2 - D, hc0, ⟨_, f1.symm⟩, ⟨_, f2.symm⟩, ?_⟩
    intro P hP
    have hcm : e ^ 2 - D ∈ IsLocalRing.maximalIdeal R := by
      rw [hm]; exact Ideal.mem_span_singleton_self _
    have hcP := map_mem ι δ D hδ hsp hP hcm
    have hprod : (δ - ι e) * (δ - ι (-e)) ∈ P := by
      have e1 : (δ - ι e) * (δ - ι (-e)) = -((δ - ι e) * (-(δ - ι (-e)))) := by ring
      rw [e1, f1]
      exact P.neg_mem hcP
    rcases hP.isPrime.mem_or_mem hprod with h | h
    · exact Or.inl (eq_span_of_factor ι δ D hδ hsp e _ _ hm f1 hP h)
    · exact Or.inr (eq_span_of_factor ι δ D hδ hsp (-e) _ _ hm f2 hP h)
  · push_neg at hsq
    exact ⟨ι ϖ, ι ϖ, ϖ, hϖ0, dvd_rfl, dvd_rfl, fun P hP =>
      Or.inl (eq_span_of_nonsquare ι δ D hδ hsp ϖ hϖ hsq hP)⟩

end Quad

section Place

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem at_place {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F)
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧
      IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  obtain ⟨O', hOC, hOB'⟩ := exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
  have hOB : ∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    (hO y).trans ((hOC y).symm.trans (hOB' y))
  have hpq : ∀ p q : K, p ∈ Rs → q ∈ Rs →
      algebraMap K (K ⊗[F] E) p + algebraMap K (K ⊗[F] E) q * B 1 ∈ O := by
    intro p q hp hq
    have h := coord_two B hB0 p q
    refine (hOB _).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [h.1]; exact hp
    · rw [h.2]; exact hq
  have hRmem : ∀ c ∈ Rs, algebraMap K (K ⊗[F] E) c ∈ O := by
    intro c hc
    simpa using hpq c 0 hc Rs.zero_mem
  have hδO : B 1 ∈ O := by
    have := hpq 0 1 Rs.zero_mem Rs.one_mem
    rwa [map_zero, map_one, zero_add, one_mul] at this
  let ι : (v.adicCompletionIntegers F) →+* O :=
    ((algebraMap K (K ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      (fun x => hRmem x x.2)
  let δ : O := ⟨B 1, hδO⟩
  let D' : v.adicCompletionIntegers F := ⟨algebraMap F K D, hDR⟩
  have hδ : δ * δ = ι D' := Subtype.ext hBD
  have hsp : ∀ y : O, ∃ p q : v.adicCompletionIntegers F, y = ι p + ι q * δ := fun y => by
    have hy := (hOB y).1 y.2
    exact ⟨⟨_, hy 0⟩, ⟨_, hy 1⟩, Subtype.ext (eq_coord B hB0 y)⟩
  have hunit : ∀ r : v.adicCompletionIntegers F, IsUnit r ↔ Valued.v (r : K) = 1 := fun r =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have hDu : IsUnit D' := (hunit D').2 hD1
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := (hunit 2).2 (by
    rw [show ((2 : v.adicCompletionIntegers F) : K) = 2 from
      map_ofNat (v.adicCompletionIntegers F).subtype 2]
    exact hv2)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨π₁, π₂, c, hc, d1, d2, hmax⟩ := exists_gens ι δ D' hδ hsp hDu h2u ϖ
    hϖ.maximalIdeal_eq hϖ.ne_zero
  have hcK : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hcu : IsUnit (((ι c : O)) : K ⊗[F] E) :=
    (IsUnit.mk0 (c : K) hcK).map (algebraMap K (K ⊗[F] E))
  have key : ∀ π : O, π ∣ ι c → IsUnit (π : K ⊗[F] E) := by
    rintro π ⟨w, hw⟩
    have h1 : (((ι c : O)) : K ⊗[F] E) = (π : K ⊗[F] E) * (w : K ⊗[F] E) :=
      congrArg Subtype.val hw
    rw [h1] at hcu
    exact isUnit_of_mul_isUnit_left hcu
  exact ⟨π₁, π₂, hmax, key π₁ d1, key π₂ d2⟩

end Place

theorem maximal_ideals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∃ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) ∧ IsUnit (π₁ : Fv F v ⊗[F] E) ∧ IsUnit (π₂ : Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB O hO
  exact at_place b b₂ D hb0 hD v hD1 h21 hBC hCB O hO

end GlobalTheory.CompanionTheory.SW.QuadMaxIdeal
