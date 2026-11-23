import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory CptModel

namespace CoordInhab

variable {o K : Type} [CommRing o] [Field K] [Algebra o K]

theorem inv_mem_of_span_eq_top {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (S : Subring K) (h1 : ∀ a : o, algebraMap o K a ∈ S)
    (h2 : ∀ j, algebraMap o K (x j) / algebraMap o K (x c) ∈ S) : (algebraMap o K (x c))⁻¹ ∈ S := by
  have h1mem : (1 : o) ∈ Submodule.span o (Set.range x) := by
    have h : (1 : o) ∈ Ideal.span (Set.range x) := by
      rw [hx]
      exact Submodule.mem_top
    exact h
  have key : ∀ y ∈ Submodule.span o (Set.range x),
      algebraMap o K y / algebraMap o K (x c) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact h2 j
    | zero =>
      rw [map_zero, zero_div]
      exact S.zero_mem
    | add y z _ _ hy hz =>
      rw [map_add, add_div]
      exact S.add_mem hy hz
    | smul r y _ hy =>
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact S.mul_mem (h1 r) hy
  have h := key 1 h1mem
  rwa [map_one, one_div] at h

theorem algebraMap_mem_regAt (p : Cpt (pt (algebraMap o K))) (a : o) :
    algebraMap o K a ∈ regAt (pt (algebraMap o K)) p :=
  RingHom.mem_range.2 ⟨tS p.1 a, genMap_toStalk _ p a⟩

variable [IsFractionRing o K]

theorem genPt_specializes (q : Spec (CommRingCat.of o)) : genPt (pt (algebraMap o K)) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  change (genPt (pt (algebraMap o K))).asIdeal ≤ _
  rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective o K)]
  exact bot_le

theorem inChart_iff {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) (c : κ)
    (p : Cpt (pt (algebraMap o K))) :
    InChart (pt (algebraMap o K)) (fun j => algebraMap o K (x j)) c p ↔ x c ∉ p.1.asIdeal := by
  have hinj := IsFractionRing.injective o K
  constructor
  · rintro ⟨hne, hrat⟩ hmem
    have hne' : algebraMap o K (x c) ≠ 0 := hne
    have hinv : (algebraMap o K (x c))⁻¹ ∈ regAt (pt (algebraMap o K)) p :=
      inv_mem_of_span_eq_top x hx c _ (algebraMap_mem_regAt p) hrat
    obtain ⟨b, s, hs, -, hbs⟩ := (mem_regAt_iff _ p _).1 hinv
    apply hs
    have hsb : algebraMap o K s = algebraMap o K (b * x c) := by
      rw [map_mul, ← hbs, mul_comm ((algebraMap o K (x c))⁻¹) (algebraMap o K s), mul_assoc,
        inv_mul_cancel₀ hne', mul_one]
    rw [hinj hsb]
    exact p.1.asIdeal.mul_mem_left b hmem
  · intro hnot
    have hne : algebraMap o K (x c) ≠ 0 := by
      intro h0
      apply hnot
      rw [(map_eq_zero_iff _ hinj).1 h0]
      exact p.1.asIdeal.zero_mem
    exact ⟨hne, fun c' => (mem_regAt_iff _ p _).2 ⟨x c', x c, hnot, hne, div_mul_cancel₀ _ hne⟩⟩

theorem exists_pow_mul_eq (t : o) (a : K)
    (h : ∀ p : Cpt (pt (algebraMap o K)), t ∉ p.1.asIdeal → a ∈ regAt (pt (algebraMap o K)) p) :
    ∃ (n : ℕ) (b : o), a * algebraMap o K t ^ n = algebraMap o K b := by
  let J : Ideal o :=
    { carrier := {s | ∃ b : o, a * algebraMap o K s = algebraMap o K b}
      add_mem' := by
        rintro u v ⟨b, hb⟩ ⟨b', hb'⟩
        exact ⟨b + b', by rw [map_add, map_add, mul_add, hb, hb']⟩
      zero_mem' := ⟨0, by rw [map_zero, mul_zero]⟩
      smul_mem' := by
        rintro r u ⟨b, hb⟩
        exact ⟨r * b, by rw [smul_eq_mul, map_mul, map_mul, ← hb]; ring⟩ }
  have hJ : ∀ s, s ∈ J ↔ ∃ b : o, a * algebraMap o K s = algebraMap o K b := fun s => Iff.rfl
  have ht : t ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra htP
    let q : Spec (CommRingCat.of o) := (⟨P, hP⟩ : PrimeSpectrum o)
    obtain ⟨a', s, hs, -, hs'⟩ := (mem_regAt_iff (algebraMap o K) ⟨q, genPt_specializes q⟩ a).1
      (h ⟨q, genPt_specializes q⟩ htP)
    exact hs (hJP ((hJ s).2 ⟨a', hs'⟩))
  obtain ⟨n, hn⟩ := ht
  obtain ⟨b, hb⟩ := (hJ _).1 hn
  exact ⟨n, b, by rw [← map_pow]; exact hb⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

end CoordInhab

open CoordInhab

theorem coordTie_spec (o K : Type) [CommRing o] [IsDomain o] [Field K] [Algebra o K] [IsFractionRing o K]
    {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) :
    CoordTie o (Spec.map (CommRingCat.ofHom (algebraMap o K))) (fun j => algebraMap o K (x j)) := by
  refine ⟨isCptGen_fractionRing, ?_, ?_, ?_⟩
  · intro p
    by_contra hall
    push Not at hall
    have hsub : Ideal.span (Set.range x) ≤ p.1.asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      by_contra hj
      exact hall j ((inChart_iff x hx j p).2 hj)
    rw [hx] at hsub
    exact p.1.isPrime.ne_top (top_le_iff.1 hsub)
  · intro c _
    refine ⟨(Spec (CommRingCat.of o)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of o)).inv (x c)),
      (isAffineOpen_top _).basicOpen _, fun q => ?_⟩
    have hmem : q ∈ (Spec (CommRingCat.of o)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of o)).inv (x c)) ↔ x c ∉ q.asIdeal := by
      rw [basicOpen_eq_of_affine]
      exact PrimeSpectrum.mem_basicOpen _ _
    rw [hmem]
    constructor
    · intro hq
      exact ⟨genPt_specializes q, (inChart_iff x hx c _).2 hq⟩
    · rintro ⟨h, hch⟩
      exact (inChart_iff x hx c _).1 hch
  · intro c hc a
    constructor
    · intro ha p hp
      obtain ⟨-, hrat⟩ := hp
      induction ha using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hrat j
      | algebraMap r => exact algebraMap_mem_regAt p r
      | add y z _ _ hy hz => exact add_mem hy hz
      | mul y z _ _ hy hz => exact mul_mem hy hz
    · intro ha
      have hinv : (algebraMap o K (x c))⁻¹ ∈ (Algebra.adjoin o
          (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c))).toSubring :=
        inv_mem_of_span_eq_top x hx c _
          (fun r => Subalgebra.algebraMap_mem
            (Algebra.adjoin o (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c))) r)
          (fun j => Algebra.subset_adjoin ⟨j, rfl⟩)
      have hinv' : (algebraMap o K (x c))⁻¹ ∈ Algebra.adjoin o
          (Set.range fun j => algebraMap o K (x j) / algebraMap o K (x c)) := hinv
      obtain ⟨n, b, hb⟩ := exists_pow_mul_eq (x c) a (fun p hp => ha p ((inChart_iff x hx c p).2 hp))
      have hc' : algebraMap o K (x c) ≠ 0 := hc
      have hab : a = algebraMap o K b * ((algebraMap o K (x c))⁻¹) ^ n := by
        rw [← hb, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc', one_pow, mul_one]
      rw [hab]
      exact mul_mem (Subalgebra.algebraMap_mem _ b) (pow_mem hinv' n)

theorem ValAt.unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (hξ : IsCptGen ξ) (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hs, s, hsa, rfl⟩ := h
  obtain ⟨hs', s', hsa', rfl⟩ := h'
  exact congrArg (Scheme.stalkClosedPointTo z).hom (hξ.inj ⟨centre z, hs⟩ (hsa.trans hsa'.symm))

namespace CoordInhab

theorem span_two_three : Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h2 : (2 : ℤ) ∈ Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) :=
    Ideal.subset_span ⟨0, by simp⟩
  have h3 : (3 : ℤ) ∈ Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) :=
    Ideal.subset_span ⟨1, by simp⟩
  have e : (1 : ℤ) = 3 - 2 := by norm_num
  rw [e]
  exact Ideal.sub_mem _ h3 h2

theorem coordTie_two_three :
    CoordTie ℤ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) :=
  coordTie_spec ℤ ℚ ![2, 3] span_two_three

theorem charts_two_three (c : Fin 2) :
    (∃ p, InChart (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) c p) ∧
    ∃ p, ¬ InChart (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) c p := by
  constructor
  · refine ⟨CptModel.self _, (inChart_iff _ span_two_three c _).2 ?_⟩
    intro hmem
    change _ ∈ (genPt (pt (algebraMap ℤ ℚ))).asIdeal at hmem
    rw [genPt_asIdeal, RingHom.mem_ker] at hmem
    fin_cases c <;> simp at hmem
  · fin_cases c
    · refine ⟨CptModel.two, fun hc => ?_⟩
      apply (inChart_iff _ span_two_three _ _).1 hc
      show _ ∈ Ideal.span {(2 : ℤ)}
      exact Ideal.subset_span (by simp)
    · refine ⟨⟨(⟨Ideal.span {3}, (Ideal.span_singleton_prime (by norm_num)).2 Int.prime_three⟩ :
          PrimeSpectrum ℤ), genPt_specializes _⟩, fun hc => ?_⟩
      apply (inChart_iff _ span_two_three _ _).1 hc
      show _ ∈ Ideal.span {(3 : ℤ)}
      exact Ideal.subset_span (by simp)

end CoordInhab

end GlobalTheory.CompanionTheory.Ar
