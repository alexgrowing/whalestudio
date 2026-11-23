import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NearOfAdjoin

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem near_of_adjoin {P L : Type} [CommRing P] [CommRing L] [Algebra P L] (G : Set L)
    (hG : ∀ g ∈ G, IsNilpotent g) (x : L) (hx : x ∈ Algebra.adjoin P G) :
    ∃ p : P, IsNilpotent (x - algebraMap P L p) :=
  _root_.UpperTheory.Reformulated.B.Qg2.near_of_adjoin G hG x hx

private theorem unit_of_near {S : Type} [CommRing S] {x u : S} (h : IsNilpotent (x - u)) (hu : IsUnit u) :
    IsUnit x := by
  have := h.isUnit_add_right_of_commute hu (Commute.all _ _)
  simpa using this

private theorem local_of_near {P S : Type} [CommRing P] [IsLocalRing P] [CommRing S] [Nontrivial S] [Algebra P S]
    (h : ∀ x : S, ∃ p : P, IsNilpotent (x - algebraMap P S p)) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨p, hp⟩ := h x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p with hu | hu
  · exact Or.inl (unit_of_near hp (hu.map _))
  · refine Or.inr (unit_of_near (u := algebraMap P S (1 - p)) ?_ (hu.map _))
    have := hp.neg
    convert this using 1
    rw [map_sub, map_one]; ring

private theorem nil_mem_max {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsNilpotent x) :
    x ∈ maximalIdeal S := fun hu => by
  obtain ⟨n, hn⟩ := h
  exact not_isUnit_zero (hn ▸ hu.pow n)

private theorem bound_fin {R : Type} [CommRing R] (S : Subalgebra (PowerSeries R) (LaurentSeries R))
    [Module.Finite (PowerSeries R) S] :
    ∃ N : ℕ, ∀ y ∈ S, ∃ q : PowerSeries R,
      algebraMap (PowerSeries R) (LaurentSeries R) q = (PowerSeries.X : PowerSeries R) ^ N • y := by
  have hfg : S.toSubmodule.FG := Module.Finite.iff_fg.1 ‹_›
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨⟨b, N, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) t
  refine ⟨N, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span (PowerSeries R) (t : Set (LaurentSeries R)) := by
    rw [ht]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem g hg => exact hb g hg
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add, hp, hq, smul_add]⟩
  | smul r a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨r * p, by rw [map_mul, hp, ← Algebra.smul_def, smul_comm]⟩

private theorem alg_monomial {R : Type} [CommRing R] (n : ℕ) (x : R) :
    algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.C x * PowerSeries.X ^ n)
      = HahnSeries.single (n : ℤ) x := by
  show HahnSeries.ofPowerSeries ℤ R _ = _
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem UpperTheory.V.Ws.sxLaur :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], IsNilpotent (maximalIdeal R) → ∀ c : ℕ, ∃ (S : Type) (_ : CommRing S) (_ : Algebra Λ S) (_ : IsCO Λ S) (e : S →+* LaurentSeries R), Laur Λ c e := by
  intro Λ _ _ R _ _ hR hnil c
  haveI hP : IsCO Λ (PowerSeries R) := co_mvps Λ R Unit
  have hnilx : ∀ x ∈ maximalIdeal R, IsNilpotent x := fun x hx => by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have := Ideal.pow_mem_pow hx k
    rw [hk] at this
    simpa using this
  have hnils : ∀ (n : ℤ), ∀ x ∈ maximalIdeal R, IsNilpotent (HahnSeries.single n x : LaurentSeries R) :=
    fun n x hx => by
      obtain ⟨k, hk⟩ := hnilx x hx
      exact ⟨k, by rw [HahnSeries.single_pow, hk, map_zero]⟩
  obtain ⟨s, hs⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  let G : Set (LaurentSeries R) := (fun x => HahnSeries.single (-(c : ℤ)) x) '' (s : Set R)
  have hGfin : G.Finite := s.finite_toSet.image _
  have hG : ∀ g ∈ G, IsNilpotent g := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnils _ x (hs ▸ Ideal.subset_span hx)
  let S := Algebra.adjoin (PowerSeries R) G
  haveI hfin : Module.Finite (PowerSeries R) S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hGfin fun g hg => by
      obtain ⟨k, hk⟩ := hG g hg
      exact ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
  have hnear : ∀ x : S, ∃ p : PowerSeries R, IsNilpotent (x - algebraMap _ S p) := fun x => by
    obtain ⟨p, k, hk⟩ := near_of_adjoin G hG x.1 x.2
    exact ⟨p, k, Subtype.ext hk⟩
  haveI : IsLocalRing S := local_of_near hnear
  letI : Algebra Λ S := ((algebraMap (PowerSeries R) S).comp (algebraMap Λ (PowerSeries R))).toAlgebra
  haveI : IsScalarTower Λ (PowerSeries R) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomap : (maximalIdeal S).comap (algebraMap (PowerSeries R) S) = maximalIdeal (PowerSeries R) :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal S))
  have hin : ∀ p ∈ maximalIdeal (PowerSeries R), algebraMap _ S p ∈ maximalIdeal S := fun p hp => by
    rw [← hcomap] at hp; exact hp
  haveI hS : IsCO Λ S := co_finite Λ (PowerSeries R) S fun x => by
    obtain ⟨p, hp⟩ := hnear x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) p
    refine ⟨a, ?_⟩
    have := (maximalIdeal S).add_mem (nil_mem_max hp) (hin _ ha)
    convert this using 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; ring
  have hXmax : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := fun hu => by
    have := PowerSeries.isUnit_constantCoeff _ hu
    simp at this
  refine ⟨S, inferInstance, inferInstance, hS, S.val.toRingHom, Subtype.val_injective, fun x => ?_, ?_, ?_⟩
  · have := alg_monomial 0 (algebraMap Λ R x)
    rw [pow_zero, mul_one, ← PowerSeries.algebraMap_apply] at this
    exact this
  · rintro n x (hn | ⟨hn, hx⟩)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      refine ⟨algebraMap _ S (PowerSeries.C x * PowerSeries.X ^ k), hin _ ?_, alg_monomial k x⟩
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hXmax k (by exact_mod_cast hn))
    · have h1 : ∀ x ∈ Ideal.span (s : Set R), (HahnSeries.single (-(c : ℤ)) x : LaurentSeries R) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem g hg => exact Algebra.subset_adjoin ⟨g, hg, rfl⟩
        | zero => rw [map_zero]; exact S.zero_mem
        | add a b _ _ ha hb => rw [HahnSeries.single_add]; exact S.add_mem ha hb
        | smul r a _ ha =>
          have := S.mul_mem (S.algebraMap_mem (PowerSeries.C r * PowerSeries.X ^ 0)) ha
          rw [alg_monomial, HahnSeries.single_mul_single] at this
          simpa using this
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (a := n + c) (by omega)
      have h2 := S.mul_mem (S.algebraMap_mem (PowerSeries.C 1 * PowerSeries.X ^ k)) (h1 x (hs ▸ hx))
      rw [alg_monomial, HahnSeries.single_mul_single, one_mul, ← hk, add_neg_cancel_right] at h2
      obtain ⟨j, hj⟩ := hnils n x hx
      exact ⟨⟨_, h2⟩, nil_mem_max ⟨j, Subtype.ext hj⟩, rfl⟩
  · intro n
    obtain ⟨N, hN⟩ := bound_fin S
    have hrad : maximalIdeal S ≤ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := by
      intro y hy
      obtain ⟨p, hp⟩ := hnear y
      have hp0 : PowerSeries.constantCoeff p ∈ maximalIdeal R := fun hu =>
        hy (unit_of_near hp ((PowerSeries.isUnit_iff_constantCoeff.2 hu).map _))
      obtain ⟨q, hq⟩ : (PowerSeries.X : PowerSeries R) ∣ p - PowerSeries.C (PowerSeries.constantCoeff p) :=
        PowerSeries.X_dvd_iff.2 (by simp)
      have e1 : y = (y - algebraMap _ S p) + algebraMap _ S (PowerSeries.C (PowerSeries.constantCoeff p))
          + algebraMap (PowerSeries R) S PowerSeries.X * algebraMap _ S q := by
        rw [← map_mul, ← hq, map_sub]; ring
      have hz : ∀ z : S, IsNilpotent z →
          z ∈ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := fun z ⟨k, hk⟩ =>
        ⟨k, hk ▸ Ideal.zero_mem _⟩
      rw [e1]
      refine Ideal.add_mem _ (Ideal.add_mem _ (hz _ hp) (hz _ (((hnilx _ hp0).map _).map _))) ?_
      exact Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨e * (n.natAbs + 1 + N), fun y hy => ?_⟩
    rw [pow_mul] at hy
    have hy2 := Ideal.pow_right_mono he _ hy
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy2
    obtain ⟨z, rfl⟩ := hy2
    obtain ⟨q, hq⟩ := hN z.1 z.2
    have e2 : S.val.toRingHom (algebraMap (PowerSeries R) S PowerSeries.X ^ (n.natAbs + 1 + N) * z)
        = algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.X ^ (n.natAbs + 1) * q) := by
      rw [map_mul (algebraMap (PowerSeries R) (LaurentSeries R)), hq, Algebra.smul_def, ← mul_assoc, ← map_mul,
        ← pow_add, ← map_pow]
      rfl
    rw [e2]
    show ((PowerSeries.X ^ (n.natAbs + 1) * q : PowerSeries R) : LaurentSeries R).coeff n = 0
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_X_pow_mul']
    simp
