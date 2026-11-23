import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.IsCMOfIsRegularLocalRing
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF

theorem height_eq_of_isMaximal_of_field {k B : Type*} [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨s, hs⟩ := exists_height_of_isMaximal_of_field k B
  rw [hs M hM, hs N hN]

theorem height_eq_of_isMaximal_of_intCast_eq_zero {B : Type*} [CommRing B] [IsDomain B]
    [Algebra.FiniteType ℤ B] (n : ℤ) (hn0 : n ≠ 0) (hnB : (n : B) = 0)
    (M N : Ideal B) (hM : M.IsMaximal) (hN : N.IsMaximal) : M.height = N.height := by
  obtain ⟨p, hpC⟩ := CharP.exists B
  have hdvd : (p : ℤ) ∣ n := by
    first
      | exact (CharP.intCast_eq_zero_iff B p n).mp hnB
      | exact (CharP.int_cast_eq_zero_iff B p n).mp hnB
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hdvd
    exact hn0 hdvd
  have hp : p.Prime := (CharP.char_is_prime_or_zero B p).resolve_right hp0
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) B := ZMod.algebra B p
  haveI : Algebra.FiniteType (ZMod p) B := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) B
  exact height_eq_of_isMaximal_of_field (k := ZMod p) M N hM hN

theorem height_eq_ringKrullDim_of_forall {B : Type*} [CommRing B]
    (hB : ∀ M N : Ideal B, M.IsMaximal → N.IsMaximal → M.height = N.height)
    (M : Ideal B) (hM : M.IsMaximal) : (M.height : WithBot ℕ∞) = ringKrullDim B := by
  haveI := hM.isPrime
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun p => ?_
    obtain ⟨N, hN, hpN⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    haveI := hN.isPrime
    have h1 : Order.height p ≤ Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) :=
      Order.height_mono (show p ≤ ⟨N, hN.isPrime⟩ from hpN)
    have h2 : N.height = Order.height (⟨N, hN.isPrime⟩ : PrimeSpectrum B) := by
      have hmem : N ∈ N.minimalPrimes := by
        rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton N
      unfold Ideal.height
      apply le_antisymm
      · exact iInf₂_le N hmem
      · exact le_iInf₂ fun J hJ =>
          Order.height_mono (show (⟨N, hN.isPrime⟩ : PrimeSpectrum B) ≤ ⟨J, hJ.1.1⟩ from hJ.1.2)
    rw [hB M N hM hN, h2]
    exact_mod_cast h1

theorem finiteRingKrullDim_mvPolynomialInt_quot {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] : FiniteRingKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ ℤ ⧸ P)
    rw [hb] at h0
    exact absurd h0 (by simp)
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_quotient_le P)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  rw [← Nat.cast_one, ← Nat.cast_add]
  rw [← WithBot.coe_natCast]
  exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))

theorem finiteRingKrullDim_quot {B : Type*} [CommRing B] [FiniteRingKrullDim B] (q : Ideal B)
    [q.IsPrime] : FiniteRingKrullDim (B ⧸ q) := by
  have hle : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_quotient_le q
  have htop : ringKrullDim B ≠ ⊤ := (finiteRingKrullDim_iff_ne_bot_and_top.mp inferInstance).2
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  have hne : ringKrullDim (B ⧸ q) ≠ ⊥ :=
    (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial).ne'
  exact ⟨hne, ne_top_of_le_ne_top htop hle⟩

private theorem ideal_height_eq_order_height_primeSpectrum {R : Type*} [CommRing R] (N : Ideal R) [hN : N.IsPrime] :
    N.height = Order.height (⟨N, hN⟩ : PrimeSpectrum R) := by
  have hmem : N ∈ N.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton N
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le N hmem
  · exact le_iInf₂ fun J hJ =>
      Order.height_mono (show (⟨N, hN⟩ : PrimeSpectrum R) ≤ ⟨J, hJ.1.1⟩ from hJ.1.2)

theorem height_int_of_isMaximal (M : Ideal ℤ) (hM : M.IsMaximal) : M.height = 1 := by
  haveI := hM.isPrime
  rw [ideal_height_eq_order_height_primeSpectrum M]
  have hMbot : M ≠ ⊥ := by
    intro h
    subst h
    exact Int.not_isField (Ring.isField_iff_maximal_bot.mpr hM)
  have hmin : ∀ z : PrimeSpectrum ℤ, z < ⟨M, hM.isPrime⟩ → IsMin z := by
    intro z hz
    have hz' : z.asIdeal < M := hz
    have hz0 : z.asIdeal = ⊥ := by
      by_contra hne
      have hmax : z.asIdeal.IsMaximal := by
        first
          | exact z.isPrime.isMaximal hne
          | exact Ring.DimensionLEOne.maximalOfPrime hne z.isPrime
          | exact Ideal.IsPrime.to_maximal_ideal z.isPrime hne
      exact (ne_of_lt hz') (hmax.eq_of_le hM.ne_top (le_of_lt hz'))
    intro w _
    show z.asIdeal ≤ w.asIdeal
    rw [hz0]
    exact bot_le
  have hx : ¬ IsMin (⟨M, hM.isPrime⟩ : PrimeSpectrum ℤ) := by
    intro h
    have hlt : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum ℤ) < ⟨M, hM.isPrime⟩ :=
      show (⊥ : Ideal ℤ) < M from bot_lt_iff_ne_bot.mpr hMbot
    exact lt_irrefl _ (lt_of_lt_of_le hlt (h (le_of_lt hlt)))
  apply le_antisymm
  · first
      | (rw [Order.height_eq_iSup_lt_height]
         refine iSup₂_le fun z hz => ?_
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         simp)
      | (show Order.height _ ≤ ((1 : ℕ) : ℕ∞)
         rw [Order.height_le_coe_iff]
         intro z hz
         rw [Order.height_eq_zero.mpr (hmin z hz)]
         exact zero_lt_one)
  · first
      | exact Order.one_le_height_iff.mpr hx
      | exact ENat.one_le_iff_ne_zero.mpr (fun h0 => hx (Order.height_eq_zero.mp h0))

theorem height_mvPolynomial_int_fin_of_isMaximal :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) ℤ)), M.IsMaximal → M.height = n + 1
  | 0, M, hM => by
    let e := MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_int_of_isMaximal _ hM']
    simp
  | n + 1, M, hM => by
    have := int_isJacobsonRing
    let e := (MvPolynomial.finSuccEquiv ℤ n).toRingEquiv
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_polynomial_of_isMaximal
      (height_mvPolynomial_int_fin_of_isMaximal n) _ hM']
    push_cast
    ring

private theorem order_height_comap_ringEquiv_symm {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : PrimeSpectrum A) :
    Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x) = Order.height x := by
  have sm1 : StrictMono (PrimeSpectrum.comap (e.symm : B →+* A)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.symm.surjective (congrArg PrimeSpectrum.asIdeal h)
  have sm2 : StrictMono (PrimeSpectrum.comap (e : A →+* B)) := by
    intro p q hpq
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
    intro h
    apply hpq.ne
    apply PrimeSpectrum.ext
    exact Ideal.comap_injective_of_surjective _ e.surjective (congrArg PrimeSpectrum.asIdeal h)
  have hcomp : PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x) = x := by
    apply PrimeSpectrum.ext
    ext a
    simp
  apply le_antisymm
  · calc Order.height (PrimeSpectrum.comap (e.symm : B →+* A) x)
        ≤ Order.height (PrimeSpectrum.comap (e : A →+* B) (PrimeSpectrum.comap (e.symm : B →+* A) x)) :=
          Order.height_le_height_apply_of_strictMono _ sm2 _
      _ = Order.height x := by rw [hcomp]
  · exact Order.height_le_height_apply_of_strictMono _ sm1 x

theorem height_eq_of_isMaximal_mvPolynomial_int {σ : Type*} [Finite σ]
    (M N : Ideal (MvPolynomial σ ℤ)) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  let e : MvPolynomial σ ℤ ≃+* MvPolynomial (Fin n) ℤ := (MvPolynomial.renameEquiv ℤ eσ).toRingEquiv
  have key : ∀ I : Ideal (MvPolynomial σ ℤ), I.IsMaximal → I.height = n + 1 := by
    intro I hI
    haveI := hI
    haveI := hI.isPrime
    have hJ : (Ideal.comap (e.symm : MvPolynomial (Fin n) ℤ →+* MvPolynomial σ ℤ) I).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    haveI := hJ.isPrime
    have h1 := height_mvPolynomial_int_fin_of_isMaximal n _ hJ
    rw [ideal_height_eq_order_height_primeSpectrum] at h1 ⊢
    rw [← h1]
    exact (order_height_comap_ringEquiv_symm e _).symm
  rw [key M hM, key N hN]

theorem height_eq_height_add_of_isRegularRing {R : Type*} [CommRing R] [IsRegularRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hA : ReciprocityTheory.CA.IsCM (Localization.AtPrime q) :=
    ReciprocityTheory.CA.isCM_of_isRegularLocalRing _
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  have : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p inferInstance hdisj
  have e := hA.height_add_ringKrullDim_quotient (p.map (algebraMap R (Localization.AtPrime q)))
  rw [IsLocalization.height_map_of_disjoint q.primeCompl p hdisj,
    ReciprocityTheory.CA.ringKrullDim_localization_quotient_eq_height p q hpq,
    IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at e
  exact_mod_cast e.symm

theorem le_add_one_of_add_eq (a b D : WithBot ℕ∞) (x c : ℕ∞) (hx : x ≠ ⊤) (hc : c ≤ 1)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hD : D ≠ ⊤) (h1 : a + x = D) (h2 : b + ((x + c : ℕ∞) : WithBot ℕ∞) = D) :
    a ≤ b + 1 := by
  lift a to ℕ∞ using ha
  lift b to ℕ∞ using hb
  subst h1
  have h2' : b + (x + c) = a + x := by exact_mod_cast h2
  have hD' : a + x ≠ ⊤ := by
    intro h; apply hD; rw [← WithBot.coe_add, h] <;> rfl
  have ha' : a ≠ ⊤ := fun h => hD' (by rw [h, top_add])
  have hb' : b ≠ ⊤ := fun h => hD' (by rw [← h2', h, top_add])
  have hc' : c ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc
  lift a to ℕ using ha'
  lift b to ℕ using hb'
  lift x to ℕ using hx
  lift c to ℕ using hc'
  have hc2 : c ≤ 1 := by exact_mod_cast hc
  have h3 : b + (x + c) = a + x := by exact_mod_cast h2'
  have h4 : a ≤ b + 1 := by omega
  exact_mod_cast h4

theorem specialFibre_dim_ge {σ : Type*} [Finite σ] (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap MvPolynomial.C = ⊥) (ℓ : ℤ) (hℓ : Prime ℓ)
    (q : Ideal (MvPolynomial σ ℤ ⧸ P))
    (hq : q ∈ (Ideal.span {((ℓ : ℤ) : MvPolynomial σ ℤ ⧸ P)}).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ ringKrullDim ((MvPolynomial σ ℤ ⧸ P) ⧸ q) + 1 := by
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨Q, hQdef⟩ : ∃ Q : Ideal (MvPolynomial σ ℤ), Q = q.comap (Ideal.Quotient.mk P) := ⟨_, rfl⟩
  have hQp : Q.IsPrime := hQdef ▸ Ideal.comap_isPrime _ _
  have hPQ : P ≤ Q := fun x hx => by
    rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact q.zero_mem
  have hQq : Q.map (Ideal.Quotient.mk P) = q := by
    rw [hQdef]; exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q

  have : (Ideal.span {((ℓ : ℤ) : MvPolynomial σ ℤ ⧸ P)}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hq1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq

  have hcat := height_eq_height_add_of_isRegularRing P Q hPQ
  rw [hQq] at hcat

  have := int_isJacobsonRing
  have hfin : FiniteRingKrullDim (MvPolynomial σ ℤ) := by
    have h0 := finiteRingKrullDim_mvPolynomialInt_quot (⊥ : Ideal (MvPolynomial σ ℤ))
    rw [finiteRingKrullDim_iff_ne_bot_and_top] at h0 ⊢
    rwa [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial σ ℤ))] at h0
  have hdP := dim_quot_add_height height_eq_of_isMaximal_mvPolynomial_int P
  have hdQ := dim_quot_add_height height_eq_of_isMaximal_mvPolynomial_int Q
  rw [hcat] at hdQ
  have hAq : ringKrullDim ((MvPolynomial σ ℤ ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P)) =
      ringKrullDim (MvPolynomial σ ℤ ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
  rw [hQq] at hAq
  rw [hAq]
  exact le_add_one_of_add_eq _ _ _ _ _ Ideal.height_ne_top_of_isPrime hq1
    (ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial)
    (ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial) ringKrullDim_ne_top hdP hdQ

theorem height_eq_of_isMaximal_int_charZero {σ : Type*} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : P.comap MvPolynomial.C = ⊥)
    (M : Ideal (MvPolynomial σ ℤ ⧸ P)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  set A := MvPolynomial σ ℤ ⧸ P
  have := finiteRingKrullDim_mvPolynomialInt_quot P
  have hAft : Algebra.FiniteType ℤ A := (inferInstance : Algebra.FiniteType ℤ (MvPolynomial σ ℤ)).of_surjective
    (Ideal.Quotient.mkₐ ℤ P) (Ideal.Quotient.mkₐ_surjective ℤ P)
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top) ?_

  have hcast : ∀ n : ℤ, ((n : ℤ) : A) = Ideal.Quotient.mk P (MvPolynomial.C n) := fun n => by
    rw [← map_intCast (Ideal.Quotient.mk P), ← map_intCast (MvPolynomial.C : ℤ →+* _), Int.cast_id]
  set Mz := M.comap (Int.castRingHom A)
  have hMz : Mz ≠ ⊥ := by
    intro h0
    have hb : M.comap ((Ideal.Quotient.mk P).comp MvPolynomial.C) = ⊥ := by
      rw [← h0]
      congr 1
    obtain ⟨q', hq', hlt⟩ := exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective M hM.isPrime hb
    exact hlt.ne (hM.eq_of_le hq'.ne_top hlt.le)
  obtain ⟨ℓ, hℓMz, hℓ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (Ideal.comap_isPrime _ _) hMz
  have hℓM : ((ℓ : ℤ) : A) ∈ M := hℓMz
  obtain ⟨q, hq, hqM⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {((ℓ : ℤ) : A)}) (J := M)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hℓM))
  have hqp : q.IsPrime := hq.1.1
  have hℓq : ((ℓ : ℤ) : A) ∈ q := hq.1.2 (Ideal.subset_span rfl)
  have hℓ0 : ((ℓ : ℤ) : A) ≠ 0 := by
    intro h
    rw [hcast, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP, Ideal.mem_bot] at h
    exact hℓ.ne_zero h
  have hq0 : q ≠ ⊥ := fun h => hℓ0 (by rw [h, Ideal.mem_bot] at hℓq; exact hℓq)
  have hqh : 1 ≤ q.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]; exact hq0
  have := finiteRingKrullDim_quot q
  have : @Algebra.FiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
    convert hAft.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)
    exact Subsingleton.elim _ _
  have hEq : ∀ M N : Ideal (A ⧸ q), M.IsMaximal → N.IsMaximal → M.height = N.height :=
    height_eq_of_isMaximal_of_intCast_eq_zero (B := A ⧸ q) ℓ hℓ.ne_zero (by
      rw [← map_intCast (Ideal.Quotient.mk q), Ideal.Quotient.eq_zero_iff_mem]; exact hℓq)
  have hMb : (M.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
  have h1 := height_add_height_map_le (q := q) (M := M) hqM
  have h2 := height_eq_ringKrullDim_of_forall hEq _ hMb
  have h3 := specialFibre_dim_ge P hP ℓ hℓ q hq
  calc ringKrullDim A ≤ ringKrullDim (A ⧸ q) + 1 := h3
    _ = ((M.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) + ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [h2]; rfl
    _ ≤ ((M.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) + (q.height : WithBot ℕ∞) :=
        add_le_add le_rfl (WithBot.coe_le_coe.mpr hqh)
    _ = ((q.height + (M.map (Ideal.Quotient.mk q)).height : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add, add_comm]
    _ ≤ M.height := WithBot.coe_le_coe.mpr h1

theorem height_eq_of_isMaximal_int {σ : Type*} [Finite σ] (P : Ideal (MvPolynomial σ ℤ))
    [P.IsPrime] (M N : Ideal (MvPolynomial σ ℤ ⧸ P)) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  by_cases hP : P.comap MvPolynomial.C = ⊥
  · have h1 := height_eq_of_isMaximal_int_charZero P hP M hM
    have h2 := height_eq_of_isMaximal_int_charZero P hP N hN
    exact_mod_cast h1.trans h2.symm
  · obtain ⟨n, hnP, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hq : Algebra.FiniteType ℤ (MvPolynomial σ ℤ ⧸ P) := by
      first
        | infer_instance
        | exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ ℤ P)
            (Ideal.Quotient.mkₐ_surjective ℤ P)
    refine @height_eq_of_isMaximal_of_intCast_eq_zero _ _ _ ?_ n hn0 ?_ M N hM hN
    · first
        | exact hq
        | (convert hq using 1 <;> first
            | exact Subsingleton.elim _ _
            | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm)
    have e1 : (MvPolynomial.C n : MvPolynomial σ ℤ) = (n : MvPolynomial σ ℤ) := eq_intCast MvPolynomial.C n
    have e2 : ((n : ℤ) : MvPolynomial σ ℤ ⧸ P) = Ideal.Quotient.mk P (n : MvPolynomial σ ℤ) :=
      (map_intCast _ n).symm
    rw [e2, Ideal.Quotient.eq_zero_iff_mem, ← e1]
    exact hnP

end ReciprocityTheory.ChartRestriction.G.Geo.DimF
