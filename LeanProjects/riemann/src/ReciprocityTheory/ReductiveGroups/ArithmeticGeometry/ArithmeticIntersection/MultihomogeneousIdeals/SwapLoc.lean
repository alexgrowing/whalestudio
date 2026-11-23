import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree

namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc

open ReciprocityTheory.ChartRestriction.G.AI

theorem length_localizedModule_quot_eq {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (S : Submonoid R) (V : Ideal R) (x : R)
    (hS : ∀ s ∈ S, IsUnit (algebraMap R T s))
    (hsurj : ∀ y : T, ∃ r : R, ∃ s ∈ S, algebraMap R T r = y * algebraMap R T s)
    (hker : ∀ r : R, algebraMap R T r = 0 → ∃ s ∈ S, s * r ∈ V)
    (hV : ∀ v ∈ V, algebraMap R T v = 0) :
    Module.length (Localization S) (LocalizedModule S (R ⧸ (V ⊔ Ideal.span {x}))) =
      Module.length T (T ⧸ Ideal.span {algebraMap R T x}) := by
  classical
  let φ : Localization S →+* T := IsLocalization.lift (M := S) (S := Localization S)
    (fun s : S => hS s.1 s.2)
  have hφ : ∀ r : R, φ (algebraMap R (Localization S) r) = algebraMap R T r :=
    fun r => IsLocalization.lift_eq _ r
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨r, s, hs, h⟩ := hsurj y
    refine ⟨IsLocalization.mk' (Localization S) r ⟨s, hs⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    rw [h, mul_comm]
  letI : Algebra (Localization S) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization S) T := IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  set I := V ⊔ Ideal.span {x}
  set J : Ideal T := Ideal.span {algebraMap R T x}
  have hI : ∀ a ∈ I, (Algebra.ofId R (T ⧸ J)) a = 0 := by
    intro a ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply R T (T ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Submodule.mem_sup.mp ha |>.elim fun v ⟨hv, y, hy, e⟩ => ?_
    rw [← e, map_add, hV v hv, zero_add]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let g : (R ⧸ I) →ₗ[R] T ⧸ J := (Ideal.Quotient.liftₐ I (Algebra.ofId R (T ⧸ J)) hI).toLinearMap
  have hg : ∀ r : R, g (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J (algebraMap R T r) := by
    intro r
    simp [g, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  haveI : IsLocalizedModule S g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · obtain ⟨u, hu⟩ := hS s.1 s.2
      refine (Module.End.isUnit_iff _).2 ⟨fun a b h => ?_, fun m => ⟨(↑u⁻¹ : T) • m, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        have h2 : (↑u⁻¹ : T) • ((s : R) • a) = (↑u⁻¹ : T) • ((s : R) • b) := by rw [h]
        rwa [← algebraMap_smul T (s : R) a, ← algebraMap_smul T (s : R) b, ← hu, smul_smul,
          smul_smul, Units.inv_mul, one_smul, one_smul] at h2
      · simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul T (s : R), ← hu, smul_smul, Units.mul_inv, one_smul]
    · obtain ⟨τ, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨r, s, hs, h⟩ := hsurj τ
      refine ⟨(Ideal.Quotient.mk I r, ⟨s, hs⟩), ?_⟩
      rw [hg, h, Submonoid.smul_def, ← algebraMap_smul T (s : R), Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm]
    · obtain ⟨r₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
      obtain ⟨r₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
      rw [hg, hg, Ideal.Quotient.eq, ← map_sub] at h
      obtain ⟨τ, hτ⟩ := Ideal.mem_span_singleton'.mp h
      obtain ⟨r', s', hs', h'⟩ := hsurj τ
      have h0 : algebraMap R T (s' * (r₁ - r₂) - r' * x) = 0 := by
        rw [map_sub, map_mul, map_mul, ← hτ, h']; ring
      obtain ⟨s'', hs'', hv⟩ := hker _ h0
      refine ⟨⟨s'' * s', mul_mem hs'' hs'⟩, ?_⟩
      rw [Submonoid.smul_def, Submonoid.smul_def]
      show (s'' * s') • Ideal.Quotient.mk I r₁ = (s'' * s') • Ideal.Quotient.mk I r₂
      rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
        Ideal.Quotient.eq]
      have : s'' * s' * r₁ - s'' * s' * r₂ = s'' * (s' * (r₁ - r₂) - r' * x) + s'' * r' * x := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hv)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  let e : LocalizedModule S (R ⧸ I) ≃ₗ[Localization S] T ⧸ J :=
    (IsLocalizedModule.iso S g).extendScalarsOfIsLocalization S (Localization S)
  rw [e.length_eq]
  exact Module.length_eq_of_surjective hφs

def IsLocData (R T : Type*) [CommRing R] [CommRing T] [Algebra R T] (S : Submonoid R)
    (V : Ideal R) : Prop :=
  (∀ s ∈ S, IsUnit (algebraMap R T s)) ∧
  (∀ y : T, ∃ r : R, ∃ s ∈ S, algebraMap R T r = y * algebraMap R T s) ∧
  (∀ r : R, algebraMap R T r = 0 → ∃ s ∈ S, s * r ∈ V) ∧
  (∀ v ∈ V, algebraMap R T v = 0)

theorem isLocData_atPrime_quot {R : Type*} [CommRing R] (V Z : Ideal R) [Z.IsPrime]
    (hVZ : V ≤ Z) [(Z.map (Ideal.Quotient.mk V)).IsPrime] :
    IsLocData R (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) Z.primeCompl V := by
  have hcm : Ideal.comap (Ideal.Quotient.mk V) (Z.map (Ideal.Quotient.mk V)) = Z := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hVZ]
  have hmem : ∀ s : R, Ideal.Quotient.mk V s ∈ Z.map (Ideal.Quotient.mk V) ↔ s ∈ Z := fun s => by
    rw [← Ideal.mem_comap, hcm]
  have halg : ∀ r : R, algebraMap R (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) r =
      algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) (Ideal.Quotient.mk V r) :=
    fun r => by rw [IsScalarTower.algebraMap_apply R (R ⧸ V), Ideal.Quotient.algebraMap_eq]
  refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · rw [halg]
    exact IsLocalization.map_units _
      (⟨Ideal.Quotient.mk V s, fun h' => hs ((hmem s).1 h')⟩ : (Z.map (Ideal.Quotient.mk V)).primeCompl)
  · obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Z.map (Ideal.Quotient.mk V)).primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (m : R ⧸ V)
    refine ⟨a, t, ?_, ?_⟩
    · intro htZ
      apply m.2
      rw [← ht]
      exact (hmem t).2 htZ
    · rw [halg, halg, ht]
      exact (IsLocalization.mk'_spec _ _ m).symm
  · rw [halg, IsLocalization.map_eq_zero_iff (Z.map (Ideal.Quotient.mk V)).primeCompl] at hr
    obtain ⟨m, hm⟩ := hr
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (m : R ⧸ V)
    refine ⟨t, ?_, ?_⟩
    · intro htZ
      apply m.2
      rw [← ht]
      exact (hmem t).2 htZ
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht]
      exact hm
  · rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero]

section LocData

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {S : Submonoid R} {V : Ideal R}

theorem IsLocData.not_mem_of_isPrime (h : IsLocData R T S V) {P : Ideal T} [hP : P.IsPrime]
    {s : R} (hs : s ∈ S) : algebraMap R T s ∉ P := by
  intro hmem
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (h.1 s hs))

theorem IsLocData.atPrime (h : IsLocData R T S V) (P : Ideal T) [hP : P.IsPrime] :
    IsLocData R (Localization.AtPrime P) (P.comap (algebraMap R T)).primeCompl V := by
  have halg : ∀ r : R, algebraMap R (Localization.AtPrime P) r =
      algebraMap T (Localization.AtPrime P) (algebraMap R T r) :=
    fun r => IsScalarTower.algebraMap_apply R T _ r
  refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · rw [halg]
    exact IsLocalization.map_units _ (⟨algebraMap R T s, hs⟩ : P.primeCompl)
  · obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨r1, s1, hs1, h1⟩ := h.2.1 x
    obtain ⟨r2, s2, hs2, h2⟩ := h.2.1 (m : T)
    refine ⟨r1 * s2, r2 * s1, ?_, ?_⟩
    · show algebraMap R T (r2 * s1) ∉ P
      rw [map_mul, h2]
      intro hmem
      rcases Ideal.IsPrime.mem_or_mem hP hmem with hm | hm
      · rcases Ideal.IsPrime.mem_or_mem hP hm with hm | hm
        · exact m.2 hm
        · exact h.not_mem_of_isPrime hs2 hm
      · exact h.not_mem_of_isPrime hs1 hm
    · simp only [halg, map_mul, h1, h2]
      rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x m]
      ring
  · rw [halg, IsLocalization.map_eq_zero_iff P.primeCompl] at hr
    obtain ⟨m, hm⟩ := hr
    obtain ⟨r', s', hs', h'⟩ := h.2.1 (m : T)
    have h0 : algebraMap R T (r' * r) = 0 := by
      rw [map_mul, h', mul_assoc, mul_comm (algebraMap R T s'), ← mul_assoc, hm, zero_mul]
    obtain ⟨s'', hs'', hV⟩ := h.2.2.1 _ h0
    refine ⟨s'' * r', ?_, by rw [mul_assoc]; exact hV⟩
    show algebraMap R T (s'' * r') ∉ P
    rw [map_mul, h']
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem hP hmem with hm' | hm'
    · exact h.not_mem_of_isPrime hs'' hm'
    · rcases Ideal.IsPrime.mem_or_mem hP hm' with hm' | hm'
      · exact m.2 hm'
      · exact h.not_mem_of_isPrime hs' hm'
  · rw [halg, h.2.2.2 v hv, map_zero]

theorem IsLocData.quot (h : IsLocData R T S V) (P : Ideal T) :
    IsLocData R (T ⧸ P) S (P.comap (algebraMap R T)) := by
  refine ⟨fun s hs => (h.1 s hs).map (Ideal.Quotient.mk P), fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, s, hs, hrs⟩ := h.2.1 y'
    refine ⟨r, s, hs, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, hrs, map_mul]
  · refine ⟨1, S.one_mem, ?_⟩
    rw [one_mul, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  · rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    exact hv

theorem IsLocData.le_of_comap_le (h : IsLocData R T S V) {P P' : Ideal T} [hP' : P'.IsPrime]
    (hle : P.comap (algebraMap R T) ≤ P'.comap (algebraMap R T)) : P ≤ P' := by
  intro y hy
  obtain ⟨r, s, hs, hrs⟩ := h.2.1 y
  have hr : r ∈ P.comap (algebraMap R T) := by
    rw [Ideal.mem_comap, hrs]
    exact P.mul_mem_right _ hy
  have hr' := hle hr
  rw [Ideal.mem_comap, hrs] at hr'
  rcases hP'.mem_or_mem hr' with h1 | h1
  · exact h1
  · exact absurd h1 (h.not_mem_of_isPrime hs)

theorem IsLocData.length_eq (h : IsLocData R T S V) (x : R) :
    Module.length (Localization S) (LocalizedModule S (R ⧸ (V ⊔ Ideal.span {x}))) =
      Ring.ord T (algebraMap R T x) := by
  unfold Ring.ord
  exact length_localizedModule_quot_eq S V x h.1 h.2.1 h.2.2.1 h.2.2.2

end LocData

open Classical in

noncomputable def lenAt {R : Type*} [CommRing R] (J W : Ideal R) : ℕ∞ :=
  if h : W.IsPrime then
    haveI := h
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))
  else 0

theorem lenAt_eq {R : Type*} [CommRing R] (J W : Ideal R) [hW : W.IsPrime] :
    lenAt J W = Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  rw [lenAt, dif_pos hW]

theorem length_quot_ne_top_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (I : Ideal A) (hm : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes) :
    Module.length A (A ⧸ I) ≠ ⊤ := by
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hm
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I)
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

theorem exists_prime_comap_atPrime_quot {R : Type*} [CommRing R] (V Z : Ideal R)
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] (Q : Ideal R) (hQ : Q.IsPrime) (hVQ : V ≤ Q)
    (hQZ : Q ≤ Z) :
    ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
      p.comap (algebraMap R _) = Q := by
  haveI := hQ
  haveI hQV : (Q.map (Ideal.Quotient.mk V)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVQ)
  have hd : Disjoint ((Z.map (Ideal.Quotient.mk V)).primeCompl : Set (R ⧸ V))
      (Q.map (Ideal.Quotient.mk V) : Set (R ⧸ V)) :=
    Set.disjoint_left.2 fun x hx hxQ => hx (Ideal.map_mono hQZ hxQ)
  refine ⟨(Q.map (Ideal.Quotient.mk V)).map
      (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)))),
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQV hd, ?_⟩
  rw [IsScalarTower.algebraMap_eq R (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))),
    ← Ideal.comap_comap]
  have hcm := IsLocalization.comap_map_of_isPrime_disjoint (Z.map (Ideal.Quotient.mk V)).primeCompl
    (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) hQV hd
  rw [show Ideal.comap (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
      (Ideal.map (algebraMap (R ⧸ V) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
        (Q.map (Ideal.Quotient.mk V))) = Q.map (Ideal.Quotient.mk V) from hcm]
  rw [Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hVQ]

section Local

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R}
  {V Z : Ideal R} [Z.IsPrime]

theorem IsLocData.comap_le (h : IsLocData R A Z.primeCompl V) (p : Ideal A) [p.IsPrime] :
    p.comap (algebraMap R A) ≤ Z := by
  intro r hr
  by_contra hz
  exact h.not_mem_of_isPrime (show r ∈ Z.primeCompl from hz) hr

theorem IsLocData.le_comap (h : IsLocData R A S V) (p : Ideal A) :
    V ≤ p.comap (algebraMap R A) := by
  intro v hv
  rw [Ideal.mem_comap, h.2.2.2 v hv]
  exact p.zero_mem

theorem IsLocData.eq_of_comap_eq (h : IsLocData R A S V) {p p' : Ideal A} [p.IsPrime]
    [p'.IsPrime] (e : p.comap (algebraMap R A) = p'.comap (algebraMap R A)) : p = p' := le_antisymm (h.le_of_comap_le e.le) (h.le_of_comap_le e.ge)

theorem IsLocData.map_eq_zero_iff [hV : V.IsPrime] (h : IsLocData R A Z.primeCompl V)
    (hVZ : V ≤ Z) (r : R) : algebraMap R A r = 0 ↔ r ∈ V := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsr⟩ := h.2.2.1 r h0
    rcases hV.mem_or_mem hsr with h1 | h1
    · exact absurd (hVZ h1) hs
    · exact h1
  · exact h.2.2.2 r

theorem IsLocData.comap_maximalIdeal [IsLocalRing A] (h : IsLocData R A Z.primeCompl V)
    (hex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z) :
    (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = Z := by
  obtain ⟨p, hp, hpZ⟩ := hex
  apply le_antisymm (h.comap_le _)
  rw [← hpZ]
  exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hp.ne_top)

theorem IsLocData.height_eq_one_iff [IsDomain A] [IsNoetherianRing A] [V.IsPrime]
    (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f : R} (hfV : f ∉ V) (p : Ideal A) [hp : p.IsPrime] :
    (p.height = 1 ∧ algebraMap R A f ∈ p) ↔
      p.comap (algebraMap R A) ∈ (V ⊔ Ideal.span {f}).minimalPrimes := by
  have hf0 : algebraMap R A f ≠ 0 := fun e => hfV ((h.map_eq_zero_iff hVZ f).mp e)
  have hpb : ∀ q : Ideal A, q.IsPrime → algebraMap R A f ∈ q → 1 ≤ q.height := by
    intro q hq hfq
    haveI := hq
    rw [Order.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.height_eq_zero_iff_eq_bot] at h0
    exact hf0 (by rw [← Ideal.mem_bot, ← h0]; exact hfq)
  have hsup : ∀ q : Ideal A, algebraMap R A f ∈ q →
      V ⊔ Ideal.span {f} ≤ q.comap (algebraMap R A) :=
    fun q hq => sup_le (h.le_comap q) (Ideal.span_le.mpr (by simpa using hq))
  constructor
  · rintro ⟨h1, hfp⟩
    refine ⟨⟨Ideal.comap_isPrime _ _, hsup p hfp⟩, fun Q ⟨hQ, hQle⟩ hQp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hex Q hQ (le_sup_left.trans hQle) (hQp.trans (h.comap_le p))
    haveI := hq
    have hqp : q ≤ p := h.le_of_comap_le hQp
    have hfq : algebraMap R A f ∈ q :=
      hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    rcases hqp.lt_or_eq with hlt | heq
    · exfalso
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h2 := hpb q hq hfq
      rw [h1] at h3
      generalize q.height = a at h2 h3
      cases a with
      | top => simp at h3
      | coe a => norm_cast at h2 h3; omega
    · rw [heq]
  · intro hmin
    have hfp : algebraMap R A f ∈ p :=
      hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    refine ⟨le_antisymm ?_ (hpb p hp hfp), hfp⟩
    apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {algebraMap R A f})
    refine ⟨⟨hp, Ideal.span_le.mpr (by simpa using hfp)⟩, fun q ⟨hq, hqle⟩ hqp => ?_⟩
    haveI := hq
    have hfq : algebraMap R A f ∈ q := hqle (Ideal.mem_span_singleton_self _)
    have := hmin.2 ⟨Ideal.comap_isPrime _ _, hsup q hfq⟩ (Ideal.comap_mono hqp)
    exact h.le_of_comap_le this

theorem IsLocData.maximalIdeal_mem_minimalPrimes [IsLocalRing A]
    (h : IsLocData R A Z.primeCompl V) (hZex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z)
    {f t : R} (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) :
    IsLocalRing.maximalIdeal A ∈
      (Ideal.span {algebraMap R A f, algebraMap R A t}).minimalPrimes := by
  have hc := h.comap_maximalIdeal hZex
  have hfZ : f ∈ Z :=
    hZ.1.2 (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have htZ : t ∈ Z := hZ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  refine ⟨⟨inferInstance, ?_⟩, fun q ⟨hq, hqle⟩ _ => ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · show f ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
      rw [hc]; exact hfZ
    · show t ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
      rw [hc]; exact htZ
  · haveI := hq
    have hfq : algebraMap R A f ∈ q := hqle (Ideal.subset_span (Set.mem_insert _ _))
    have htq : algebraMap R A t ∈ q :=
      hqle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have hZq : Z ≤ q.comap (algebraMap R A) :=
      hZ.2 ⟨Ideal.comap_isPrime _ _, sup_le (sup_le (h.le_comap q)
        (Ideal.span_le.mpr (by simpa using hfq))) (Ideal.span_le.mpr (by simpa using htq))⟩
        (h.comap_le q)
    exact h.le_of_comap_le (hc ▸ hZq)

theorem IsLocData.ringKrullDim_eq_two [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [V.IsPrime] (h : IsLocData R A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal R, Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Q)
    {f t : R} (hfV : f ∉ V) (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes)
    (hft : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, W ≤ Z → t ∉ W) : ringKrullDim A = 2 := by
  classical
  have hZex := hex Z ‹_› hVZ le_rfl
  have hm := h.maximalIdeal_mem_minimalPrimes hZex hZ
  have hc := h.comap_maximalIdeal hZex
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have hle : (IsLocalRing.maximalIdeal A).height ≤ 2 := by
    have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := {algebraMap R A f, algebraMap R A t}) (by simpa using hm)
    exact this.trans (by exact_mod_cast Finset.card_le_two)
  have hfZ : V ⊔ Ideal.span {f} ≤ Z := le_sup_left.trans hZ.1.2
  obtain ⟨W, hW, hWZ⟩ := Ideal.exists_minimalPrimes_le hfZ
  obtain ⟨p, hp, hpW⟩ := hex W hW.1.1 (le_sup_left.trans hW.1.2) hWZ
  haveI := hp
  have hf0 : algebraMap R A f ≠ 0 := fun e => hfV ((h.map_eq_zero_iff hVZ f).mp e)
  have hfp : algebraMap R A f ∈ p := by
    show f ∈ p.comap (algebraMap R A)
    rw [hpW]; exact hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have htp : algebraMap R A t ∉ p := by
    show t ∉ p.comap (algebraMap R A)
    rw [hpW]; exact hft W hW hWZ
  have htm : algebraMap R A t ∈ IsLocalRing.maximalIdeal A := by
    show t ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
    rw [hc]; exact hZ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  have hbot : (⊥ : Ideal A) < p :=
    bot_lt_iff_ne_bot.mpr fun e => hf0 (by rw [← Ideal.mem_bot, ← e]; exact hfp)
  have hpm : p < IsLocalRing.maximalIdeal A :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) fun e => htp (e ▸ htm)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hpm
  rw [Ideal.height_bot] at h1
  have h3 : (IsLocalRing.maximalIdeal A).height = 2 := by
    generalize (IsLocalRing.maximalIdeal A).height = b at h2 hle ⊢
    generalize p.height = a at h1 h2
    cases b with
    | top => simp at hle
    | coe b =>
      cases a with
      | top => simp at h2
      | coe a => norm_cast at h1 h2 hle ⊢; omega
  rw [h3]
  rfl

end Local

end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
