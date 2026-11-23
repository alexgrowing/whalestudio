import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AevalEqZeroOfHomogeneousComponent

open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section Dimension

theorem ringKrullDim_eq_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsIntegral R S] :
    ringKrullDim S = ringKrullDim R := by
  refine le_antisymm (Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun P Q h => Ideal.IsIntegral.comap_lt_comap (R := R) h) (iSup_le fun l => ?_)
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S)
    l.head.asIdeal (by simp [(RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective R S)])
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

theorem exists_ringKrullDim_eq_and_trdeg_eq (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by
  obtain ⟨s, g, hg, hg'⟩ := exists_integral_inj_algHom_of_fg K A
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  refine ⟨s, ?_, ?_⟩
  · simp [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) K) A, ringKrullDim_eq_zero_of_field]
  · simp [← trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A), trdeg_eq_zero]

end Dimension

section Principal

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in

theorem isPrincipal_of_forall_C_mem {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (E : Ideal (Polynomial R)) [hE : E.IsPrime]
    (h : ∀ r, Polynomial.C r ∈ E → r = 0) : E.IsPrincipal := by
  by_cases h0 : E = ⊥
  · rw [h0]; exact bot_isPrincipal
  obtain ⟨g, hg, hgp⟩ := hE.exists_mem_prime_of_ne_bot h0
  have hP : (Ideal.span {g}).IsPrime := (Ideal.span_singleton_prime hgp.ne_zero).2 hgp
  have hle : Ideal.span {g} ≤ E := (Ideal.span_singleton_le_iff_mem _).2 hg
  let F := FractionRing R
  let M : Submonoid (Polynomial R) := (nonZeroDivisors R).map Polynomial.C
  have hd : Disjoint (M : Set (Polynomial R)) E := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨r, hr, rfl⟩ hrE
    exact nonZeroDivisors.ne_zero hr (h r hrE)
  have hd' : Disjoint (M : Set (Polynomial R)) (Ideal.span {g} : Ideal _) := hd.mono_right hle
  have h1 := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial F) E hE hd
  have h2 := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial F) _ hP hd'
  have h3 : (Ideal.span {g}).map (algebraMap (Polynomial R) (Polynomial F)) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R F)).2 hgp.ne_zero
  have h4 := (IsPrime.to_maximal_ideal h3).eq_of_le h1.ne_top (Ideal.map_mono hle)
  refine ⟨g, ?_⟩
  rw [← IsLocalization.under_map_of_isPrime_disjoint M (Polynomial F) hE hd, ← h4,
    IsLocalization.under_map_of_isPrime_disjoint M (Polynomial F) hP hd']

theorem isPrincipal_of_forall_rename_mem {K ι ι' : Type*} [Field K] [Finite ι'] (ε : ι ≃ Option ι')
    (E : Ideal (MvPolynomial ι K)) [E.IsPrime]
    (h : ∀ g : MvPolynomial ι' K, rename (fun v => ε.symm (some v)) g ∈ E → g = 0) :
    E.IsPrincipal := by
  let e : MvPolynomial ι K ≃ₐ[K] Polynomial (MvPolynomial ι' K) :=
    (renameEquiv K ε).trans (optionEquivLeft K ι')
  have he (g : MvPolynomial ι' K) :
      e.symm (Polynomial.C g) = rename (fun v => ε.symm (some v)) g := by
    have : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (fun v => ε.symm (some v)) := by
      ext v : 1
      simp [e]
    exact DFunLike.congr_fun this g
  have := isPrincipal_of_forall_C_mem (E.comap e.symm) fun g hg => h g (he g ▸ hg)
  obtain ⟨g, hg⟩ := this
  refine ⟨e.symm g, ?_⟩
  have h2 := Ideal.map_comap_of_surjective e.symm e.symm.surjective E
  rw [← h2, hg]
  simp [Ideal.map_span]

end Principal

section Injective

theorem injective_of_constantCoeff {R S V : Type*} [CommRing R] [CommRing S]
    (ψ : MvPolynomial V R →+* MvPolynomial V S) (hX : ∀ v, ψ (X v) = X v)
    (h : ∀ r, constantCoeff (ψ (C r)) = 0 → r = 0) : Function.Injective ψ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  obtain ⟨a, ha, hmin⟩ := P.support.exists_minimal (support_nonempty.2 hne)
  have hmon (b : V →₀ ℕ) (r : R) : ψ (monomial b r) = ψ (C r) * monomial b 1 := by
    rw [monomial_eq, monomial_eq, map_mul, C_1, one_mul, map_finsuppProd]
    simp [hX]
  have : coeff a (ψ P) = constantCoeff (ψ (C (coeff a P))) := by
    conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
    rw [Finset.sum_eq_single a]
    · rw [hmon, coeff_mul_monomial', if_pos le_rfl, tsub_self, mul_one, constantCoeff_eq]
    · intro b hb hba
      rw [hmon, coeff_mul_monomial', if_neg]
      exact fun hle => hba (le_antisymm hle (hmin hb hle))
    · exact fun h => absurd ha h
  rw [hP, coeff_zero] at this
  exact mem_support_iff.1 ha (h _ this.symm)

theorem injective_of_eval {R S V : Type*} [CommRing R] [CommRing S]
    (ψ : MvPolynomial V R →+* MvPolynomial V S) (hX : ∀ v, ψ (X v) = X v) (c : V → R) (c' : V → S)
    (hc : ∀ v, ψ (C (c v)) = C (c' v))
    (h : ∀ r, eval c' (ψ (C r)) = 0 → r = 0) : Function.Injective ψ := by
  let τ : MvPolynomial V S →+* MvPolynomial V S := eval₂Hom C fun v => X v + C (c' v)
  let ρ : MvPolynomial V R →+* MvPolynomial V R := eval₂Hom C fun v => X v - C (c v)
  let ρ' : MvPolynomial V R →+* MvPolynomial V R := eval₂Hom C fun v => X v + C (c v)
  have h1 : ρ.comp ρ' = RingHom.id _ := by ext : 1 <;> [ext : 1; skip] <;> simp [ρ, ρ']
  have h2 : constantCoeff.comp τ = eval c' := by ext : 1 <;> [ext : 1; skip] <;> simp [τ]
  have h3 := injective_of_constantCoeff (τ.comp (ψ.comp ρ)) (fun v => by simp [τ, ρ, hX, hc])
    fun r hr => h r (by rw [← h2]; simpa [ρ] using hr)
  have h4 : Function.Injective (ψ.comp ρ) := Function.Injective.of_comp (f := τ) h3
  have hs : Function.Surjective ρ := fun x => ⟨ρ' x, DFunLike.congr_fun h1 x⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := hs x
  obtain ⟨y, rfl⟩ := hs y
  rw [h4 hxy]

theorem algebraicIndependent_div {K F β : Type*} [Field K] [Field F] [Algebra K F] {z : β → F}
    (hz : AlgebraicIndependent K z) (i₀ : β) :
    AlgebraicIndependent K fun i : {i // i ≠ i₀} => z i / z i₀ := by
  classical
  have h0 : z i₀ ≠ 0 := hz.ne_zero i₀
  let π : MvPolynomial β K →ₐ[K] MvPolynomial {i // i ≠ i₀} K :=
    aeval fun i => if h : i = i₀ then 1 else X ⟨i, h⟩
  have hπ0 : π (X i₀) = 1 := by simp [π]
  have key (P : MvPolynomial {i // i ≠ i₀} K) : ∃ (m : ℕ) (Q : MvPolynomial β K),
      aeval z Q = z i₀ ^ m * aeval (fun i : {i // i ≠ i₀} => z i / z i₀) P ∧ π Q = P := by
    induction P using MvPolynomial.induction_on with
    | C a => exact ⟨0, C a, by simp, by simp⟩
    | add p q hp hq =>
      obtain ⟨m, p', hp, hp'⟩ := hp
      obtain ⟨n, q', hq, hq'⟩ := hq
      refine ⟨m + n, p' * X i₀ ^ n + q' * X i₀ ^ m, ?_, by simp [hπ0, hp', hq']⟩
      simp only [map_add, map_mul, map_pow, aeval_X, hp, hq]
      ring
    | mul_X p i hp =>
      obtain ⟨m, p', hp, hp'⟩ := hp
      refine ⟨m + 1, p' * X i.1, ?_, by rw [map_mul, hp']; simp [π, i.2]⟩
      simp only [map_mul, aeval_X, hp]
      field_simp
      ring
  rw [algebraicIndependent_iff] at hz ⊢
  intro P hP
  obtain ⟨m, Q, hQ, rfl⟩ := key P
  rw [hz Q (by rw [hQ, hP, mul_zero]), map_zero]

end Injective

section Existence

variable {K : Type u} [Field K] {σ β : Type} [Fintype σ] [Fintype β]

theorem elimIdeal_ne_bot {p : Ideal (MvPolynomial σ K)} [hP : p.IsPrime]
    (hp : p.IsHomogeneous (homogeneousSubmodule σ K)) (hX : ∃ j, X j ∉ p)
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) ≤ (Fintype.card β : ℕ)) : elimIdeal β p ≠ ⊥ := by
  classical
  intro hE
  have hne := genericPoint_ne_zero hX
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hne
  replace hj₀ : genericPoint p j₀ ≠ 0 := hj₀
  let F := FractionRing (MvPolynomial σ K ⧸ p)
  let y : σ → F := fun j => (genericPoint p j₀)⁻¹ * genericPoint p j
  let q : Ideal (MvPolynomial σ K) := RingHom.ker (aeval y : MvPolynomial σ K →ₐ[K] F)
  have hq : q.IsPrime := RingHom.ker_isPrime _
  have hle : p ≤ q :=
    aeval_smul_eq_zero hp (fun g => (aeval_genericPoint_eq_zero_iff p g).2) _
  have h1q : X j₀ - 1 ∈ q := by simp [q, y, RingHom.mem_ker, hj₀]
  have h1p : X j₀ - 1 ∉ p := by
    intro h
    have := homogeneousComponent_mem_of_mem hp h 0
    rw [homogeneousComponent_zero] at this
    simp only [coeff_sub, coeff_zero_X, coeff_zero_one, zero_sub, map_neg, map_one,
      neg_mem_iff] at this
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 this)
  let B := MvPolynomial σ K ⧸ q
  obtain ⟨s, hs, hs'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K B
  have hlt := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk p (X j₀ - 1))
    (mem_nonZeroDivisors_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.1 h1p))
    (Ideal.Quotient.eq_zero_iff_mem.2 h1q)
  have hsβ : s + 1 ≤ Fintype.card β := by
    have := hlt.trans hdim
    rw [hs] at this
    exact_mod_cast this
  let u : σ → B := fun j => Ideal.Quotient.mk q (X j)
  have hu : IsUnit (u j₀) := by
    have : u j₀ = 1 := Ideal.Quotient.eq.2 h1q
    rw [this]; exact isUnit_one
  let χ : MvPolynomial (β × σ) K →ₐ[K]
      MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j₀} B :=
    ((linFormElim u hu Set.univ).restrictScalars K).comp (mapAlgHom (Algebra.ofId K B))
  have hχ : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : map (algebraMap K B) f ∈ Ideal.span (Set.range (linForm u : β → _)) := by
      rw [← Set.image_univ, ← ker_linFormElim u hu]
      exact hf
    let ι : B →ₐ[K] F := Ideal.kerLiftAlg (aeval y : MvPolynomial σ K →ₐ[K] F)
    have h2 := map_mem_span_linForm ι.toRingHom h1
    have h3 : ι.toRingHom.comp (algebraMap K B) = algebraMap K F := RingHom.ext ι.commutes
    rw [map_map, h3] at h2
    rw [← Ideal.mem_bot, ← hE,
      mem_elimIdeal_iff_of_generic (aeval_genericPoint_eq_zero_iff p) hne]
    refine Ideal.span_le.2 ?_ h2
    rintro _ ⟨i, rfl⟩
    have h4 (j) : ι.toRingHom (u j) = (genericPoint p j₀)⁻¹ * genericPoint p j := by
      exact (Ideal.kerLiftAlg_mk _ _).trans (aeval_X _ _)
    have : linForm (fun j => ι.toRingHom (u j)) i =
        C (genericPoint p j₀)⁻¹ * linForm (genericPoint p) i := by
      simp only [linForm, h4, Finset.mul_sum, C_mul, mul_assoc]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have h5 := trdeg_le_of_injective χ hχ
  rw [← trdeg_add_eq K B (A := MvPolynomial {v : β × σ // v ∉ elimIndices Set.univ j₀} B), hs',
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
    Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast] at h5
  have h6 : Fintype.card (β × σ) ≤
      s + Fintype.card {v : β × σ // v ∉ elimIndices Set.univ j₀} := by exact_mod_cast h5
  have h7 : Fintype.card β ≤ Fintype.card {v : β × σ // v ∈ elimIndices Set.univ j₀} :=
    Fintype.card_le_of_injective (fun i => ⟨(i, j₀), trivial, rfl⟩)
      fun a b h => congrArg (fun v => v.1.1) h
  have h8 := Fintype.card_subtype_compl fun v : β × σ => v ∈ elimIndices Set.univ j₀
  have h9 := Fintype.card_subtype_le fun v : β × σ => v ∈ elimIndices Set.univ j₀
  omega

omit [Fintype σ] in

theorem exists_algebraicIndependent_genericPoint [Finite σ] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    ∃ κ : β → σ, AlgebraicIndependent K fun i => genericPoint p (κ i) := by
  let A := MvPolynomial σ K ⧸ p
  obtain ⟨s, hs, hs'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K A
  have hsβ : s = Fintype.card β := by
    rw [hs] at hdim
    exact_mod_cast hdim
  let x : σ → A := fun j => Ideal.Quotient.mk p (X j)
  have htop : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    have : aeval x = Ideal.Quotient.mkₐ K p := algHom_ext fun j => aeval_X _ _
    rw [this]
    exact Ideal.Quotient.mk_surjective
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A :=
    ⟨fun a => isAlgebraic_algebraMap (⟨a, htop ▸ trivial⟩ : Algebra.adjoin K (Set.range x))⟩
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
  have hc := hb.cardinalMk_eq_trdeg
  rw [hs', hsβ] at hc
  obtain ⟨e⟩ : Nonempty (β ≃ t) := by
    rw [← Cardinal.lift_mk_eq', hc]
    simp
  choose κ hκ using fun i => ht (e i).2
  refine ⟨κ, ?_⟩
  have h1 := (hb.1.comp e e.injective).map'
    (f := IsScalarTower.toAlgHom K A (FractionRing A)) (IsFractionRing.injective A _)
  convert h1 using 2 with i
  simp [genericPoint, ← hκ, x, A]

theorem isPrincipal_elimIdeal [Nonempty β] {p : Ideal (MvPolynomial σ K)} [p.IsPrime]
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    (elimIdeal β p).IsPrincipal := by
  classical
  obtain ⟨κ, hκ⟩ := exists_algebraicIndependent_genericPoint hdim
  obtain ⟨i₀⟩ := ‹Nonempty β›
  let F := FractionRing (MvPolynomial σ K ⧸ p)
  let ξ : σ → F := genericPoint p
  let j₀ := κ i₀
  have h0 : ξ j₀ ≠ 0 := hκ.ne_zero i₀
  have hκ0 (i : β) (hi : i ≠ i₀) : κ i ≠ j₀ := fun h => hi (hκ.injective (congrArg ξ h))
  have : (elimIdeal β p).IsPrime := isPrime_elimIdeal ⟨j₀, fun h =>
    h0 (by rw [← aeval_genericPoint_eq_zero_iff, aeval_X] at h; exact h)⟩
  let V := β × {j : σ // j ≠ j₀}
  let W := {i : β // i ≠ i₀}
  let δ : Option (V ⊕ W) → β × σ := fun o =>
    o.elim (i₀, j₀) (Sum.elim (fun v => (v.1, v.2.1)) fun i => (i.1, j₀))
  have hδ : Function.Bijective δ := by
    constructor
    · rintro (_ | ⟨i, j, hj⟩ | ⟨i, hi⟩) (_ | ⟨i', j', hj'⟩ | ⟨i', hi'⟩) h <;>
        simp only [δ, Option.elim, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h <;>
        first | rfl | (obtain ⟨rfl, h⟩ := h; first | contradiction | (subst h; first | rfl | contradiction) | rfl)
    · rintro ⟨i, j⟩
      by_cases hj : j = j₀
      · by_cases hi : i = i₀
        · exact ⟨none, by simp [δ, hi, hj]⟩
        · exact ⟨some (.inr ⟨i, hi⟩), by simp [δ, hj]⟩
      · exact ⟨some (.inl (i, ⟨j, hj⟩)), rfl⟩
  refine isPrincipal_of_forall_rename_mem (Equiv.ofBijective δ hδ).symm _ fun g hg => ?_
  let s : β → MvPolynomial V F := fun i => -∑ k : {j : σ // j ≠ j₀}, X (i, k) * C (ξ k / ξ j₀)
  let t : β × σ → MvPolynomial V F := fun v => if h : v.2 = j₀ then s v.1 else X (v.1, ⟨v.2, h⟩)
  have ht (i : β) : ∑ j, t (i, j) * C (ξ j) = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (p := fun l => l ≠ j₀) (F := inferInstance) _ (by simp)]
    simp only [t, s, dif_pos, neg_mul, Finset.sum_mul, mul_assoc, ← C_mul, div_mul_cancel₀ _ h0]
    rw [neg_add_eq_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [dif_neg k.2]
  have hz : aeval t (rename (fun v => δ (some v)) g) = 0 := by
    refine aeval_eq_zero_of_mem_elimIdeal (ξ := fun j => C (ξ j)) (fun a ha => ?_)
      (fun h => h0 (C_eq_zero.1 (congrFun h j₀))) ht hg
    have := aeval_algebraMap_apply (MvPolynomial V F) ξ a
    rw [(aeval_genericPoint_eq_zero_iff p a).2 ha, map_zero] at this
    exact this
  let ψ : MvPolynomial V (MvPolynomial W K) →+* MvPolynomial V F :=
    eval₂Hom (aeval (fun i : W => s i.1) : MvPolynomial W K →ₐ[K] _).toRingHom X
  have hψ : ψ (sumAlgEquiv K V W g) = aeval t (rename (fun v => δ (some v)) g) := by
    have : ψ.comp (sumAlgEquiv K V W).toRingEquiv.toRingHom =
        ((aeval t).comp (rename (fun v => δ (some v))) : _ →ₐ[K] _).toRingHom := by
      refine ringHom_ext (fun a => ?_) ?_
      · simp [ψ]
      · rintro (⟨i, j, hj⟩ | i) <;> simp [ψ, δ, t, *]
    exact DFunLike.congr_fun this g
  have hinj : Function.Injective ψ := by
    refine injective_of_eval ψ (fun v => by simp [ψ])
      (fun v => if v.2.1 = κ v.1 then -1 else 0) (fun v => if v.2.1 = κ v.1 then -1 else 0)
      (fun v => by split_ifs <;> simp) fun r hr => ?_
    refine algebraicIndependent_iff.1 (algebraicIndependent_div hκ i₀) r ?_
    rw [← hr]
    have : (aeval (fun i : W => ξ (κ i) / ξ j₀) : MvPolynomial W K →ₐ[K] F).toRingHom =
        (eval fun v : V => if v.2.1 = κ v.1 then (-1 : F) else 0).comp (ψ.comp C) := by
      refine ringHom_ext (fun a => by simp [ψ]) fun i => ?_
      have : ∑ k : {j : σ // j ≠ j₀}, (if k.1 = κ i then (-1 : F) else 0) * (ξ k / ξ j₀) =
          -(ξ (κ i) / ξ j₀) := by
        rw [Finset.sum_eq_single ⟨κ i, hκ0 i i.2⟩]
        · rw [if_pos rfl]
          ring
        · intro k _ hk
          rw [if_neg fun h => hk (Subtype.ext h), zero_mul]
        · simp
      simp only [ψ, s, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply,
        eval₂Hom_C, map_neg, map_sum, map_mul, eval_X, eval_C, this]
      ring
    exact DFunLike.congr_fun this r
  rw [← hψ, map_eq_zero_iff ψ hinj, map_eq_zero_iff _ (AlgEquiv.injective _)] at hz
  exact hz

end Existence

end GlobalTheory.Chow
