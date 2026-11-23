import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticComplexMultiplication
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CmInertiaRestrictionHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegSquarePadic
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaMovesSquareRoot
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DecompositionFixesSquareRoot
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ExSplitCM

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem prime_eq_of_mem (u : HeightOneSpectrum (𝓞 F)) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : ((p : ℕ) : 𝓞 F) ∈ u.asIdeal) (h' : ((p' : ℕ) : 𝓞 F) ∈ u.asIdeal) : p = p' := by
  by_contra hne
  have hc : Nat.gcd p p' = 1 := (Nat.coprime_primes hp hp').2 hne
  have hm : (((Nat.gcd p p' : ℕ) : ℤ) : 𝓞 F) ∈ u.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab p p']
    push_cast
    exact u.asIdeal.add_mem (u.asIdeal.mul_mem_right _ h) (u.asIdeal.mul_mem_right _ h')
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem finite_primes_of_finite {B : Set (HeightOneSpectrum (𝓞 F))} (hB : B.Finite) :
    {p : ℕ | p.Prime ∧ ∃ u ∈ B, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}.Finite := by
  refine (hB.biUnion (t := fun u => {p : ℕ | p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun u _ => Set.Subsingleton.finite fun p hp p' hp' => prime_eq_of_mem u hp.1 hp'.1 hp.2 hp'.2).subset ?_
  rintro p ⟨hp, u, hu, h⟩
  exact Set.mem_biUnion hu ⟨hp, h⟩

theorem exists_mem_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show ((p : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at h2
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hne : M ≠ ⊥ := by
    intro h
    rw [h] at hle
    have h0 := hle (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_bot] at h0
    exact hp.ne_zero (by exact_mod_cast h0)
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.mem_span_singleton_self _)⟩

theorem mem_range_res_iff (K : IntermediateField F Ω) (σ : G F Ω) :
    σ ∈ (res F Ω ↥K).range ↔ ∀ x ∈ K, σ x = x := by
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => h _ x.2, rfl⟩

theorem fix_adjoin {δ : Ω} (hint : IsIntegral F δ) (s : G F Ω) (h : s δ = δ) :
    ∀ x ∈ IntermediateField.adjoin F {δ}, s x = x := by
  intro x hx
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
  have := (AlgHom.eqOn_adjoin_iff (φ := (s : Ω →ₐ[F] Ω)) (ψ := AlgHom.id F Ω)).2
    (by simpa [Set.EqOn] using h) hx
  simpa using this

theorem exists_qcm [IsTotallyReal F] [IsAlgClosure F Ω] (d : F) (δ : Ω) (hδ : δ ^ 2 = algebraMap F Ω d)
    (hd : ∀ φ : F →+* ℝ, φ d < 0) : ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ} := by
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Monic :=
      Polynomial.monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := Polynomial.natDegree_le_natDegree h1
    rwa [Polynomial.natDegree_X_pow_sub_C] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let w : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h3 := hd ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  exact ⟨⟨K, inferInstance, IsCMField.ofCMExtension F K, hrk⟩, rfl⟩

end GlobalTheory.ExSplitCM

open GlobalTheory.ExSplitCM in
theorem GlobalTheory.RealGal.exists_infinite_qcm_split_ram : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : HeightOneSpectrum (𝓞 F) → Prop), (∀ᶠ u in Filter.cofinite, T u) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range}.Infinite := by
  intro F Ω _ _ _ _ _ _ T hT v A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  let Good : Set ℕ := {p | p.Prime ∧ IsSquare (-(p : ℚ_[q])) ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr F ∧
    ∀ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → T u}
  have hGood : Good.Infinite := by
    have hbad : ({2} ∪ {p : ℕ | p ∣ (discr F).natAbs} ∪
        {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) | ¬ T u}, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}).Finite := by
      refine ((Set.finite_singleton 2).union ?_).union (finite_primes_of_finite (Filter.eventually_cofinite.1 hT))
      exact (Nat.divisors (discr F).natAbs).finite_toSet.subset fun p hp =>
        Nat.mem_divisors.2 ⟨hp, Int.natAbs_ne_zero.2 (discr_ne_zero F)⟩
    refine ((GlobalTheory.T.infinite_primes_neg_square_padic q).diff hbad).mono ?_
    rintro p ⟨⟨hp, hs⟩, hn⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_and, not_exists] at hn
    refine ⟨hp, hs, hn.1.1, fun h => hn.1.2 (Int.natCast_dvd.1 h), fun u hu => ?_⟩
    by_contra hTu
    exact hn.2 hp u hTu hu
  have hQ : ∀ p ∈ Good, ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} := by
    intro p hp
    refine exists_qcm (-(p : F)) (δ p) (by simp [hδ p]) fun φ => ?_
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.1.pos
  have hmove : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      ∀ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal →
        IsPlaceOver A' u → ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range := by
    intro p hp Q hQK u A' hu hA' hle
    obtain ⟨s, hs, hne⟩ := GlobalTheory.T.inertia_moves_square_root F Ω p hp.1 hp.2.2.1 hp.2.2.2.1 (δ p) (hδ p) u A' hu hA'
    refine hne ((mem_range_res_iff Q.K s).1 (hle hs) (δ p) ?_)
    rw [hQK]
    exact IntermediateField.mem_adjoin_simple_self F (δ p)
  have hmem : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      Q ∈ {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range} := by
    intro p hp Q hQK
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.T.decomposition_fixes_square_root F Ω v A hA q hqv (-(p : ℤ)) (δ p) (by push_cast; exact hδ p)
        (by push_cast; exact hp.2.1) s hs
    · obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
      obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
      exact ⟨u, A', hp.2.2.2.2 u hu, hA', hmove p hp Q hQK u A' hu hA'⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : QCM F Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := F) A' ≤ (res F Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds F ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  exact ⟨u, fun hall => hmove p hp Q hQK u A' hu hA' (hall A' hA'), hu⟩
