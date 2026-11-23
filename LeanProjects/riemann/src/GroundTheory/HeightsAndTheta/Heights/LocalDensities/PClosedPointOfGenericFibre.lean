import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsClosedPointGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

namespace ClosedPointOfGenericFibre

theorem height_eq_of_isMaximal_of_finiteType_int (R : Type) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] (M N : Ideal R) (hM : M.IsMaximal) (hN : N.IsMaximal) :
    M.height = N.height := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ R›
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let e := (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  have hM' : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective e e.surjective
  have hN' : (N.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective e e.surjective
  rw [← RingEquiv.height_comap e M, ← RingEquiv.height_comap e N]
  exact ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_eq_of_isMaximal_int (RingHom.ker f) _ _ hM' hN'

theorem finiteRingKrullDim_of_finiteType_int (R : Type) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] : FiniteRingKrullDim R := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType ℤ R›
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have h := ReciprocityTheory.ChartRestriction.G.Geo.DimF.finiteRingKrullDim_mvPolynomialInt_quot (RingHom.ker f)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  rw [finiteRingKrullDim_iff_ne_bot_and_top, ← ringKrullDim_eq_of_ringEquiv e]
  exact finiteRingKrullDim_iff_ne_bot_and_top.mp h

theorem finiteType_int (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] : Algebra.FiniteType ℤ R :=
  Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance

theorem isMaximal_comap_of_isMaximal (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    (M.comap (algebraMap (𝓞 F) R)).IsMaximal := by
  have : IsJacobsonRing ℤ := ReciprocityTheory.ChartRestriction.G.Geo.int_isJacobsonRing
  have : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType (𝓞 F) (R ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) M) (Ideal.Quotient.mkₐ_surjective _ M)
  have : Module.Finite (𝓞 F) (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing (𝓞 F) (R ⧸ M)
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 F) (⊥ : Ideal (R ⧸ M))
  have he : (⊥ : Ideal (R ⧸ M)).comap (algebraMap (𝓞 F) (R ⧸ M)) =
      M.comap (algebraMap (𝓞 F) R) := by
    ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  rwa [he] at h

theorem comap_ne_bot_of_isMaximal (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (hM : M.IsMaximal) :
    M.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h
  have := isMaximal_comap_of_isMaximal F R M hM
  rw [h] at this
  exact RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr this)

theorem two_le_height_of_lt {R : Type} [CommRing R] [IsDomain R] {P M : Ideal R} [P.IsPrime]
    [M.IsPrime] (hP : P ≠ ⊥) (hPM : P < M) : 2 ≤ M.height := by
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (I := ⊥) (J := P) (bot_lt_iff_ne_bot.mpr hP)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hPM
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ P.height + 1 := by gcongr
    _ ≤ M.height := h2

theorem two_le_height_of_not_isAlgebraic (F : Type) [Field F] [NumberField F] (R : Type)
    [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R]
    (hinj : Function.Injective (algebraMap (𝓞 F) R)) (hna : ¬ Algebra.IsAlgebraic (𝓞 F) R)
    (M : Ideal R) (hM : M.IsMaximal) : 2 ≤ M.height := by
  set T := Algebra.algebraMapSubmonoid R (nonZeroDivisors (𝓞 F)) with hTdef
  have hT : T ≤ nonZeroDivisors R := by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hc))
  have : IsDomain (Localization T) := IsLocalization.isDomain_localization hT

  have hS : ¬ IsField (Localization T) := by
    intro hS
    let : Field (Localization T) := hS.toField
    have : IsLocalization (Submonoid.map (algebraMap (𝓞 F) R) (nonZeroDivisors (𝓞 F)))
        (Localization T) := Localization.isLocalization
    have : Algebra.FiniteType (FractionRing (𝓞 F)) (Localization T) :=
      RingHom.finiteType_localizationPreserves (algebraMap (𝓞 F) R) (nonZeroDivisors (𝓞 F))
        (FractionRing (𝓞 F)) (Localization T) (RingHom.finiteType_algebraMap.mpr inferInstance)
    have : Module.Finite (FractionRing (𝓞 F)) (Localization T) :=
      finite_of_finite_type_of_isJacobsonRing _ _
    have : Algebra.IsAlgebraic (𝓞 F) (Localization T) :=
      (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing (𝓞 F))).mpr inferInstance
    exact hna (Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom (𝓞 F) R (Localization T))
      (IsLocalization.injective (Localization T) hT))
  obtain ⟨n, hn⟩ := Ideal.exists_maximal (Localization T)
  have hn0 : n ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hn hS
  set P := n.comap (algebraMap R (Localization T)) with hPdef
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hn0
    rw [← IsLocalization.map_under T (Localization T) n]
    change Ideal.map _ P = ⊥
    rw [h, Ideal.map_bot]
  have hPO : P.comap (algebraMap (𝓞 F) R) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_bot]
    by_contra hc0
    have hu : IsUnit (algebraMap R (Localization T) (algebraMap (𝓞 F) R c)) :=
      IsLocalization.map_units (Localization T)
        (⟨algebraMap (𝓞 F) R c, c, mem_nonZeroDivisors_of_ne_zero hc0, rfl⟩ : T)
    exact hn.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hu)
  have hPmax : ¬ P.IsMaximal := fun h => comap_ne_bot_of_isMaximal F R P h hPO
  obtain ⟨M', hM', hPM'⟩ := Ideal.exists_le_maximal P hPp.ne_top
  have hlt : P < M' := lt_of_le_of_ne hPM' (fun h => hPmax (h ▸ hM'))
  have h2 := two_le_height_of_lt hP0 hlt
  have := finiteType_int F R
  rwa [height_eq_of_isMaximal_of_finiteType_int R M M' hM hM']

theorem exists_isPrime_ne_bot_le_notMem {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (M : Ideal R) [M.IsPrime] (hM : 2 ≤ M.height) (t : R) (ht : t ≠ 0) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ P ≤ M ∧ t ∉ P := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {t})
  set s := insert (⊥ : Ideal R) hfin.toFinset with hs
  have hprime : ∀ i ∈ s, i ≠ ⊥ → i ≠ ⊥ → (id i).IsPrime := by
    intro i hi h1 _
    rcases Finset.mem_insert.mp hi with h | h
    · exact absurd h h1
    · exact (hfin.mem_toFinset.mp h).1.1
  have hnot : ¬ ((M : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), ((id i : Ideal R) : Set R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ hprime]
    rintro ⟨i, hi, hMi⟩
    rcases Finset.mem_insert.mp hi with h | h
    · subst h
      have h0 : M = ⊥ := le_bot_iff.mp hMi
      rw [h0, Ideal.height_bot] at hM
      exact absurd hM (by decide)
    · have hmin := hfin.mem_toFinset.mp h
      have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ i hmin
      have h3 := hM.trans ((Ideal.height_mono hMi).trans h1)
      exact absurd h3 (by decide)
  obtain ⟨u, huM, hu⟩ := Set.not_subset.mp hnot
  have hu' : ∀ i ∈ s, u ∉ i := fun i hi hui =>
    hu (Set.mem_biUnion (x := i) (by simpa using hi) hui)
  have hu0 : u ≠ 0 := fun h => hu' ⊥ (Finset.mem_insert_self _ _) (by rw [h]; exact Ideal.zero_mem _)
  have huQ : ∀ Q ∈ (Ideal.span {t}).minimalPrimes, u ∉ Q := fun Q hQ =>
    hu' Q (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hQ))
  obtain ⟨P, hP, hPM⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {u}) (J := M)
    ((Ideal.span_singleton_le_iff_mem M).mpr huM)
  have hPp : P.IsPrime := hP.1.1
  have huP : u ∈ P := hP.1.2 (Ideal.mem_span_singleton_self u)
  refine ⟨P, hPp, fun h => hu0 (by rw [h, Ideal.mem_bot] at huP; exact huP), hPM, fun htP => ?_⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {t}) (J := P)
    ((Ideal.span_singleton_le_iff_mem P).mpr htP)
  have hQp : Q.IsPrime := hQ.1.1
  have htQ : t ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self t)
  have hQ0 : Q ≠ ⊥ := fun h => ht (by rw [h, Ideal.mem_bot] at htQ; exact htQ)
  rcases hQP.lt_or_eq with hlt | heq
  · have h2 := two_le_height_of_lt hQ0 hlt
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {u}) P hP
    exact absurd (h2.trans h1) (by decide)
  · exact huQ Q hQ (heq ▸ huP)

theorem exists_of_height_le (F : Type) [Field F] [NumberField F] (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R],
      Function.Injective (algebraMap (𝓞 F) R) → ∀ (M : Ideal R) (g : R), M.IsMaximal → g ≠ 0 →
      M.height ≤ n → ∃ Q : Ideal R, Q.IsPrime ∧ Q ≤ M ∧ Q.comap (algebraMap (𝓞 F) R) = ⊥ ∧
        g ∉ Q ∧ Algebra.IsAlgebraic (𝓞 F) (R ⧸ Q) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ _ _ hinj M g hM hg hn
  by_cases halg : Algebra.IsAlgebraic (𝓞 F) R
  · refine ⟨⊥, Ideal.isPrime_bot, bot_le, ?_, by simpa using hg, ?_⟩
    · ext c
      rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ hinj]
    · exact ⟨fun x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective (𝓞 F) (⊥ : Ideal R) x
        exact (halg.isAlgebraic r).algHom _⟩
  have h2 := two_le_height_of_not_isAlgebraic F R hinj halg M hM
  have hp := isMaximal_comap_of_isMaximal F R M hM
  obtain ⟨h, hhp, hh0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (comap_ne_bot_of_isMaximal F R M hM)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  obtain ⟨P, hPp, hP0, hPM, htP⟩ := exists_isPrime_ne_bot_le_notMem M h2
    (algebraMap (𝓞 F) R h * g) (mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hh0) hg)
  have hgP : g ∉ P := fun hgP => htP (P.mul_mem_left _ hgP)
  have hPO : P.comap (algebraMap (𝓞 F) R) = ⊥ := by
    by_contra hne
    have hmax := Ideal.IsPrime.isMaximal (Ideal.comap_isPrime (algebraMap (𝓞 F) R) P) hne
    have heq : P.comap (algebraMap (𝓞 F) R) = M.comap (algebraMap (𝓞 F) R) :=
      hmax.eq_of_le hp.ne_top (Ideal.comap_mono hPM)
    have hhP : h ∈ P.comap (algebraMap (𝓞 F) R) := heq ▸ hhp
    exact htP (P.mul_mem_right _ hhP)
  have : Algebra.FiniteType (𝓞 F) (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) P) (Ideal.Quotient.mkₐ_surjective _ P)
  have hinj' : Function.Injective (algebraMap (𝓞 F) (R ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hc
    have hc' : c ∈ P.comap (algebraMap (𝓞 F) R) := hc
    rwa [hPO, Ideal.mem_bot] at hc'
  set M' := M.map (Ideal.Quotient.mk P) with hM'def
  have hM' : M'.IsMaximal :=
    hM.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPM)
  have hg' : Ideal.Quotient.mk P g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]

  have := finiteType_int F R
  have := finiteRingKrullDim_of_finiteType_int R
  have hsum := ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_add_height_map_le (q := P) (M := M) hPM
  have hP1 : 1 ≤ P.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hP0
  have hht : M'.height + 1 ≤ (n : ℕ∞) := by
    calc M'.height + 1 ≤ P.height + M'.height := by rw [add_comm]; gcongr
      _ ≤ M.height := hsum
      _ ≤ n := hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    rcases n with _ | k
    · exact absurd hht (by simp)
    · exact ⟨k, rfl⟩
  have hk : M'.height ≤ k := by
    rw [Nat.cast_add, Nat.cast_one] at hht
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hht
  obtain ⟨Q', hQ'p, hQ'M, hQ'O, hgQ', hQ'alg⟩ :=
    ih k (Nat.lt_succ_self k) (R ⧸ P) hinj' M' (Ideal.Quotient.mk P g) hM' hg' hk

  set Q := Q'.comap (Ideal.Quotient.mk P) with hQdef
  refine ⟨Q, Ideal.comap_isPrime _ _, ?_, ?_, hgQ', ?_⟩
  · exact (Ideal.comap_mono hQ'M).trans (ReciprocityTheory.ChartRestriction.G.Geo.DimF.comap_map_mk hPM).le
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_bot, hQdef, Ideal.mem_comap, Ideal.Quotient.mk_algebraMap,
      ← Ideal.mem_comap, hQ'O, Ideal.mem_bot]
  · refine Algebra.IsAlgebraic.of_injective (Ideal.quotientMapₐ Q' (Ideal.Quotient.mkₐ (𝓞 F) P) le_rfl) ?_
    exact Ideal.quotientMap_injective

end ClosedPointOfGenericFibre

theorem ClosedPointOfGenericFibre.proof : ClosedPointOfGenericFibre.Statement := by
  intro F _ _ R _ _ _ _ _ M g ⟨hM, hg⟩
  have hinj : Function.Injective (algebraMap (𝓞 F) R) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have h1 : (1 : R) ∈ Submodule.torsion (𝓞 F) R :=
      (Submodule.mem_torsion_iff (1 : R)).mpr
        ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, by rw [Submonoid.smul_def, Algebra.smul_def, hc, zero_mul]⟩
    rw [Module.Flat.torsion_eq_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hM.ne_top)
  exact ClosedPointOfGenericFibre.exists_of_height_le F n R hinj M g hM hg hn.symm.le

end GroundTheory.Heights₂.Heights.FourB
