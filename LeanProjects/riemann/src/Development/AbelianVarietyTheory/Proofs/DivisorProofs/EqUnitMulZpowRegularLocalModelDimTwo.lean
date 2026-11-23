import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFreeGenOfFormallyEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUnit

variable {k L : Type} [Field k] [Field L] {c : k →+* L}

theorem isNoetherianRing {Q : Subring L} (hQ : IsLocModel c Q) : IsNoetherianRing Q := by
  letI := (c.codRestrict Q hQ.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
  exact Algebra.EssFiniteType.isNoetherianRing k Q

theorem isFractionRing {Q : Subring L} (hQ : IsLocModel c Q) : IsFractionRing Q L := by
  refine IsFractionRing.of_field Q L fun z => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩

theorem exists_place_of_height_eq_one {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (p : Ideal Q) [p.IsPrime] (hp1 : p.height = 1) :
    ∃ P : Place c, P.IsPrimeOf Q ∧ ∀ a ∈ P.ring, ∃ s : Q, s ∉ p ∧ (s : L) * a ∈ Q := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q L := Localization.subalgebra.ofField L p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hp
  haveI : IsLocalization.AtPrime A p := hA
  haveI : IsDiscreteValuationRing A := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 A
  haveI : IsFractionRing A L := Localization.subalgebra.isFractionRing_ofField L _ hp
  let V : ValuationSubring L :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, fun f hf => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    have e' : f * (b.1 : L) = a := congrArg Subtype.val e
    exact ⟨b.1, b.2, by rw [mul_comm, e']; exact a.2⟩

theorem mem_of_forall_isPrimeOf {Q : Subring L} (hQ : IsLocModel c Q) [IsIntegrallyClosed Q]
    (a : L) (h : ∀ P : Place c, P.IsPrimeOf Q → a ∈ P.ring) : a ∈ Q := by
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  haveI : IsFractionRing Q L := isFractionRing hQ
  obtain ⟨y, hy⟩ := (GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := Q) (K := L) a).2
    fun p _ hp1 => by
      obtain ⟨P, hP, hs⟩ := exists_place_of_height_eq_one hQ p hp1
      obtain ⟨s, hsp, hsa⟩ := hs a (h P hP)
      exact (GlobalTheory.mem_primeLocalSubalgebra_iff p a).2 ⟨s, hsp, ⟨⟨_, hsa⟩, rfl⟩⟩
  rw [← hy]
  exact y.2

end GlobalTheory.FieldPair.AdjUnit

namespace GlobalTheory.FieldPair.AdjUnit

theorem eq_unit_mul_zpow : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
    ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  intro L _ cL Q hQ t u hm hd E hE hu G hG hP
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := isNoetherianRing hQ
  have hsp : (Ideal.span {t, u} : Ideal Q).spanFinrank ≤ 2 :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  haveI : IsRegularLocalRing Q := IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q (by
    rw [← hm, hd]; exact_mod_cast hsp)
  have huL : (u : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hu
    exact zero_ne_one hu
  have hu0 : u ≠ 0 := fun h => huL (by rw [h]; rfl)
  have hum : u ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have htm : t ∈ IsLocalRing.maximalIdeal Q := hm ▸ Ideal.subset_span (by simp)
  have hu2 : u ∉ IsLocalRing.maximalIdeal Q ^ 2 := by
    intro h2
    have hle : IsLocalRing.maximalIdeal Q ≤ Ideal.span {t} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Q)
        (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
      rw [← hm, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_sup_left (Ideal.subset_span rfl), Submodule.mem_sup_right ?_⟩
      rw [hm, smul_eq_mul, ← pow_two]
      exact h2
    have heq : IsLocalRing.maximalIdeal Q = Ideal.span {t} :=
      le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).2 htm)
    have h1 : (IsLocalRing.maximalIdeal Q).spanFinrank ≤ 1 := by
      rw [heq]
      exact (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans
        (by rw [Set.ncard_singleton])
    have h3 := ringKrullDim_le_spanFinrank_maximalIdeal Q
    rw [hd] at h3
    have h4 : ((IsLocalRing.maximalIdeal Q).spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
    have := h3.trans h4
    norm_num at this
  haveI : IsRegularLocalRing (Q ⧸ Ideal.span ({u} : Set Q)) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hum hu2
  have hdom : IsDomain (Q ⧸ Ideal.span ({u} : Set Q)) := inferInstance
  have hpr : Prime u :=
    (Ideal.span_singleton_prime hu0).1 ((Ideal.Quotient.isDomain_iff_prime _).1 hdom)
  obtain ⟨S, -, -, hSo⟩ := GlobalTheory.FieldPair.AdjModel.exists_place hQ hpr
  have hES : E.ring = S.ring := by
    by_contra h
    have := hSo E hE h
    omega
  haveI : IsIntegrallyClosed Q := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing Q).2
  set b := E.ord G with hb
  set G' : L := G * (u : L) ^ (-b) with hG'
  have hG'0 : G' ≠ 0 := mul_ne_zero hG (zpow_ne_zero _ huL)
  have hord : ∀ P : Place cL, P.IsPrimeOf Q → P.ord G' = 0 := by
    intro P hPQ
    rw [hG', P.ord_mul hG (zpow_ne_zero _ huL), P.ord_zpow]
    by_cases hPE : P.ring = E.ring
    · obtain rfl : P = E := Place.ext hPE
      rw [hu, ← hb]; ring
    · rw [hP P hPQ hPE, hSo P hPQ (hES ▸ hPE)]; ring
  have h1 : G' ∈ Q := mem_of_forall_isPrimeOf hQ G' fun P hPQ =>
    (P.ord_nonneg_iff hG'0).1 (by rw [hord P hPQ])
  have h2 : G'⁻¹ ∈ Q := mem_of_forall_isPrimeOf hQ G'⁻¹ fun P hPQ =>
    (P.ord_nonneg_iff (inv_ne_zero hG'0)).1 (by rw [P.ord_inv, hord P hPQ]; rfl)
  refine ⟨⟨G', h1⟩, IsUnit.of_mul_eq_one (a := (⟨G', h1⟩ : Q)) (⟨G'⁻¹, h2⟩ : Q)
    (Subtype.ext (mul_inv_cancel₀ hG'0)), ?_⟩
  change G = G * (u : L) ^ (-b) * (u : L) ^ b
  rw [mul_assoc, ← zpow_add₀ huL, neg_add_cancel, zpow_zero, mul_one]

end GlobalTheory.FieldPair.AdjUnit
