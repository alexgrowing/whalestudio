import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramOrder

section Abstract

open IsLocalRing Polynomial

variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]

theorem exists_eq_add_mul (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω)) (x : R) :
    ∃ a b : R₀, x = algebraMap R₀ R a + algebraMap R₀ R b * ω := by
  obtain ⟨e, he⟩ := hω.exists_right_inv
  have he' : (c ω - ω) * c e = 1 := by simpa [hc] using congrArg c he
  have hce : c e = -e := by linear_combination (-e) * he' - (c e) * he
  obtain ⟨b, hb⟩ := hfix ((x - c x) * e) (by rw [map_mul, map_sub, hc, hce]; ring)
  obtain ⟨a, ha⟩ := hfix (x - algebraMap R₀ R b * ω) (by
    rw [map_sub, map_mul, hbase, hb]
    linear_combination (x - c x) * he)
  exact ⟨a, b, by rw [ha]; ring⟩

theorem card_quot_eq_sq (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hinj : Function.Injective (algebraMap R₀ R))
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω)) (p : R₀) :
    Nat.card (R ⧸ Ideal.span {algebraMap R₀ R p}) = Nat.card (R₀ ⧸ Ideal.span {p}) ^ 2 := by
  let φ : R₀ × R₀ →+ R :=
    { toFun := fun z => algebraMap R₀ R z.1 + algebraMap R₀ R z.2 * ω
      map_zero' := by simp
      map_add' := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring }
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨a, b, h⟩ := exists_eq_add_mul c hc hbase hfix hω x
    exact ⟨(a, b), h.symm⟩
  have hind : ∀ a b : R₀, algebraMap R₀ R a + algebraMap R₀ R b * ω = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' := congrArg c h
    rw [map_add, map_mul, hbase, hbase, map_zero] at h'
    have hb : algebraMap R₀ R b = 0 :=
      hω.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap R₀ R a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  have hcomap : (Ideal.span {algebraMap R₀ R p}).toAddSubgroup.comap φ
      = (Ideal.span {p}).toAddSubgroup.prod (Ideal.span {p}).toAddSubgroup := by
    ext ⟨a, b⟩
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω y
      obtain ⟨h1, h2⟩ := hind (a - p * u) (b - p * v) (by
        have hy' : algebraMap R₀ R a + algebraMap R₀ R b * ω = _ := hy
        simp only [map_sub, map_mul]
        linear_combination hy')
      exact ⟨⟨u, sub_eq_zero.1 h1⟩, ⟨v, sub_eq_zero.1 h2⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      refine ⟨algebraMap R₀ R u + algebraMap R₀ R v * ω, ?_⟩
      show algebraMap R₀ R _ + algebraMap R₀ R _ * ω = _
      simp only [map_mul]; ring
  have h := AddSubgroup.index_comap_of_surjective
    (Ideal.span {algebraMap R₀ R p}).toAddSubgroup hφ
  rw [hcomap, AddSubgroup.index_prod] at h
  rw [sq]
  exact h.symm

theorem isPrincipalIdealRing_of_henselian [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [HenselianRing R₀ (maximalIdeal R₀)] (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω))
    (hD : ∀ r : R₀, IsUnit (algebraMap R₀ R r) → IsUnit r) :
    IsPrincipalIdealRing R := by
  obtain ⟨t, ht⟩ := hfix (ω + c ω) (by rw [map_add, hc, add_comm])
  obtain ⟨n, hn⟩ := hfix (ω * c ω) (by rw [map_mul, hc, mul_comm])
  have hDu : IsUnit (t ^ 2 - 4 * n) := by
    refine hD _ ?_
    convert hω.pow 2 using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ht, hn]
    ring
  by_cases hroot : ∃ r : R₀, r ^ 2 - t * r + n ∈ maximalIdeal R₀
  · obtain ⟨r₀, hr₀⟩ := hroot
    have hder : IsUnit (2 * r₀ - t) := by
      by_contra h
      have h1 : 2 * r₀ - t ∈ maximalIdeal R₀ := h
      have h2 : t ^ 2 - 4 * n ∈ maximalIdeal R₀ := by
        have : t ^ 2 - 4 * n = (2 * r₀ - t) * (2 * r₀ - t) - 4 * (r₀ ^ 2 - t * r₀ + n) := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hr₀)
      exact h2 hDu
    obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R₀)
      (X ^ 2 - C t * X + C n) (by monicity!) r₀ (by simpa using hr₀) (by
        have := hder.map (Ideal.Quotient.mk (maximalIdeal R₀))
        convert this using 2
        simp [one_add_one_eq_two])
    simp only [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
    obtain ⟨d, hd⟩ := hDu.exists_right_inv

    have hg : (2 * r - t) * ((2 * r - t) * d) = 1 := by linear_combination hd + 4 * d * hr
    set g := (2 * r - t) * d
    have hr' := congrArg (algebraMap R₀ R) hr
    have hg' := congrArg (algebraMap R₀ R) hg
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one, map_ofNat] at hr' hg'
    have hωω : ω * ω = algebraMap R₀ R t * ω - algebraMap R₀ R n := by rw [ht, hn]; ring
    set T := algebraMap R₀ R t
    set N := algebraMap R₀ R n
    set ρ := algebraMap R₀ R r with hρ
    set G := algebraMap R₀ R g
    obtain ⟨e, he⟩ : ∃ e, e = (ω - (T - ρ)) * G := ⟨_, rfl⟩
    have hee : e * e = e := by
      rw [he]
      linear_combination G ^ 2 * hωω - G ^ 2 * hr' + (ω - (T - ρ)) * G * hg'
    let ψ : R₀ × R₀ →+* R :=
      { toFun := fun z => algebraMap R₀ R z.1 * e + algebraMap R₀ R z.2 * (1 - e)
        map_zero' := by simp
        map_one' := by simp
        map_add' := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
        map_mul' := fun x y => by
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          linear_combination (-(algebraMap R₀ R x.1 - algebraMap R₀ R x.2)
            * (algebraMap R₀ R y.1 - algebraMap R₀ R y.2)) * hee }
    refine IsPrincipalIdealRing.of_surjective ψ fun x => ?_
    obtain ⟨a, b, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω x
    refine ⟨(a + b * r, a + b * (t - r)), ?_⟩
    show algebraMap R₀ R _ * e + algebraMap R₀ R _ * (1 - e) = _
    simp only [map_add, map_mul, map_sub]
    rw [he]
    linear_combination algebraMap R₀ R b * (ω - (T - ρ)) * hg'
  · push Not at hroot
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
    have hm := hϖ.maximalIdeal_eq
    have hunit : ∀ a b : R₀, ¬ (ϖ ∣ a ∧ ϖ ∣ b) →
        IsUnit (algebraMap R₀ R a + algebraMap R₀ R b * ω) := by
      intro a b hab
      have hN : IsUnit (a ^ 2 + t * a * b + n * b ^ 2) := by
        by_contra h
        have h1 : a ^ 2 + t * a * b + n * b ^ 2 ∈ maximalIdeal R₀ := h
        by_cases hb : IsUnit b
        · obtain ⟨v, hv⟩ := hb.exists_right_inv
          refine hroot (-(a * v)) ?_
          have : (-(a * v)) ^ 2 - t * (-(a * v)) + n
              = v ^ 2 * (a ^ 2 + t * a * b + n * b ^ 2) := by
            linear_combination (-(t * a * v) - n * (b * v + 1)) * hv
          rw [this]
          exact Ideal.mul_mem_left _ _ h1
        · have hb' : b ∈ maximalIdeal R₀ := hb
          have ha2 : a ^ 2 ∈ maximalIdeal R₀ := by
            have : a ^ 2 = (a ^ 2 + t * a * b + n * b ^ 2) - (t * a + n * b) * b := by ring
            rw [this]
            exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hb')
          have ha : a ∈ maximalIdeal R₀ := Ideal.IsPrime.mem_of_pow_mem inferInstance 2 ha2
          rw [hm, Ideal.mem_span_singleton] at ha hb'
          exact hab ⟨ha, hb'⟩
      have h2 := hN.map (algebraMap R₀ R)
      have : algebraMap R₀ R (a ^ 2 + t * a * b + n * b ^ 2)
          = (algebraMap R₀ R a + algebraMap R₀ R b * ω)
            * (algebraMap R₀ R a + algebraMap R₀ R b * c ω) := by
        simp only [map_add, map_mul, map_pow, ht, hn]; ring
      rw [this] at h2
      exact isUnit_of_mul_isUnit_left h2
    have hfac : ∀ x : R, x ≠ 0 → ∃ k : ℕ, ∃ u : R, IsUnit u ∧ x = algebraMap R₀ R ϖ ^ k * u := by
      intro x hx
      obtain ⟨a, b, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω x
      obtain ⟨d, a', b', rfl, rfl, hcop⟩ : ∃ d a' b' : R₀, a = d * a' ∧ b = d * b' ∧
          ¬ (ϖ ∣ a' ∧ ϖ ∣ b') := by
        rcases ValuationRing.dvd_total a b with ⟨z, hz⟩ | ⟨z, hz⟩
        · exact ⟨a, 1, z, by simp, hz, fun h => hϖ.not_dvd_one h.1⟩
        · exact ⟨b, z, 1, hz, by simp, fun h => hϖ.not_dvd_one h.2⟩
      have hd : d ≠ 0 := by rintro rfl; simp at hx
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
      refine ⟨k, _, (u.isUnit.map (algebraMap R₀ R)).mul (hunit a' b' hcop), ?_⟩
      simp only [map_mul, map_pow]; ring
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · rw [hI]; infer_instance
    have hpow : ∀ x ∈ I, x ≠ 0 → ∃ k : ℕ, algebraMap R₀ R ϖ ^ k ∈ I ∧ algebraMap R₀ R ϖ ^ k ∣ x := by
      intro x hx hx0
      obtain ⟨k, u, hu, rfl⟩ := hfac x hx0
      exact ⟨k, (I.mul_unit_mem_iff_mem hu).1 hx, dvd_mul_right _ _⟩
    have hex : ∃ k : ℕ, algebraMap R₀ R ϖ ^ k ∈ I := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨k, hk, -⟩ := hpow x hx hx0
      exact ⟨k, hk⟩
    refine ⟨algebraMap R₀ R ϖ ^ Nat.find hex, le_antisymm (fun x hx => ?_) ?_⟩
    · by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      obtain ⟨k, hk, hkx⟩ := hpow x hx hx0
      exact Ideal.mem_span_singleton.2 ((pow_dvd_pow _ (Nat.find_min' hex hk)).trans hkx)
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 (Nat.find_spec hex)

end Abstract

section Local

open IsLocalRing Polynomial

theorem exists_double_root {k : Type*} [Field k] [Finite k] {t n : k} (h : t ^ 2 - 4 * n = 0) :
    ∃ a, t = 2 * a ∧ n = a ^ 2 := by
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 n
    have h0 : (2 : k) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := k)
      rw [h2] at this
      exact_mod_cast this
    have ht : t ^ 2 = 0 := by linear_combination h + 2 * n * h0
    exact ⟨r, by rw [pow_eq_zero_iff two_ne_zero |>.1 ht, h0, zero_mul], by rw [hr, sq]⟩
  · have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    refine ⟨t / 2, by field_simp, ?_⟩
    field_simp
    linear_combination -h

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem algebraMap_inj (L : LocE F E) : Function.Injective (algebraMap F E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  exact (algebraMap F E).injective

theorem algebraMap_mem_iff (L : LocE F E) (c : F) : algebraMap F E c ∈ L.O ↔ c ∈ 𝒪[F] := by
  rw [L.O_def, isIntegral_algebraMap_iff (algebraMap_inj L), IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem exists_int_of_fixed (L : LocE F E) {x : E} (hx : x ∈ L.O) (h : L.cj x = x) :
    ∃ c : 𝒪[F], x = algebraMap F E c := by
  obtain ⟨a, rfl⟩ := (L.cj_fix x).1 h
  exact ⟨⟨a, (algebraMap_mem_iff L a).1 hx⟩, rfl⟩

theorem exists_trace (L : LocE F E) {x : E} (hx : x ∈ L.O) :
    ∃ c : 𝒪[F], x + L.cj x = algebraMap F E c :=
  exists_int_of_fixed L (L.O.add_mem hx (cj_mem L hx)) (by simp [L.cj_cj, add_comm])

theorem exists_norm (L : LocE F E) {x : E} (hx : x ∈ L.O) :
    ∃ c : 𝒪[F], x * L.cj x = algebraMap F E c :=
  exists_int_of_fixed L (L.O.mul_mem hx (cj_mem L hx)) (by simp [L.cj_cj, mul_comm])

theorem exists_eq_mul_of_anti (L : LocE F E) {y z : E} (hy : L.cj y = -y) (hz : L.cj z = -z)
    (hz0 : z ≠ 0) : ∃ c : F, y = algebraMap F E c * z := by
  have := L.reduced
  obtain ⟨d, hd⟩ := (L.cj_fix (z ^ 2)).1 (by simp [hz])
  obtain ⟨s, hs⟩ := (L.cj_fix (y * z)).1 (by simp [hz, hy])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hz0 (IsReduced.eq_zero z ⟨2, by rw [← hd, map_zero]⟩)
  have h1 : algebraMap F E d⁻¹ * z ^ 2 = 1 := by
    rw [← hd, ← map_mul, inv_mul_cancel₀ hd0, map_one]
  refine ⟨s * d⁻¹, ?_⟩
  rw [map_mul, hs]
  linear_combination (-y) * h1

theorem exists_mem_sub_cj_ne_zero [CharZero F] (L : LocE F E) :
    ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, L.cj x ≠ x := by
    by_contra h
    push Not at h
    have hb : Function.Bijective (Algebra.linearMap F E) :=
      ⟨algebraMap_inj L, fun x => (L.cj_fix x).1 (h x)⟩
    have := (LinearEquiv.ofBijective _ hb).finrank_eq
    rw [L.rank, Module.finrank_self] at this
    omega
  have key : ∀ (z : E) (d : 𝒪[F]), z ≠ 0 → L.cj z = -z → z ^ 2 = algebraMap F E d →
      ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 := by
    intro z d hz0 hz hd
    refine ⟨z, (L.O_def z).2 (IsIntegral.of_pow two_pos ?_), fun h => hz0 ?_⟩
    · rw [hd]; exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := d)
    · have h2 : algebraMap F E 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      rw [hz] at h
      linear_combination algebraMap F E 2⁻¹ * h - z * h2
  have hz0 : x - L.cj x ≠ 0 := fun h => hx (sub_eq_zero.1 h).symm
  have hz : L.cj (x - L.cj x) = -(x - L.cj x) := by simp [L.cj_cj]
  set z := x - L.cj x
  obtain ⟨d, hd⟩ := (L.cj_fix (z ^ 2)).1 (by simp [hz])
  by_cases hd0 : d = 0
  · exact key z 0 hz0 hz (by rw [← hd, hd0]; rfl)
  rcases ValuationRing.isInteger_or_isInteger 𝒪[F] d with ⟨d', rfl⟩ | ⟨d', hd'⟩
  · exact key z d' hz0 hz hd.symm
  · have h1 : algebraMap F E d * algebraMap F E d⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hd0, map_one]
    refine key (algebraMap F E d⁻¹ * z) d' (fun h => hz0 ?_) (by
      rw [map_mul, AlgEquiv.commutes, hz, mul_neg]) ?_
    · linear_combination algebraMap F E d * h - z * h1
    · have : (d' : F) = d⁻¹ := hd'
      rw [this, mul_pow, ← hd]
      linear_combination algebraMap F E d⁻¹ * h1

variable [IsNonarchimedeanLocalField F]

theorem exists_generator [CharZero F] (L : LocE F E) : ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 ∧
    ∀ x ∈ L.O, ∃ b : 𝒪[F], x - L.cj x = algebraMap F E b * (ω - L.cj ω) := by
  have := L.reduced
  have hdisc : ∀ x ∈ L.O, ∃ d : 𝒪[F], (x - L.cj x) ^ 2 = algebraMap F E d := fun x hx =>
    exists_int_of_fixed L (L.O.pow_mem (L.O.sub_mem hx (cj_mem L hx)) 2) (by
      rw [map_pow, map_sub, L.cj_cj]; ring)
  let S : Set 𝒪[F] := {d | ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 ∧ (ω - L.cj ω) ^ 2 = algebraMap F E d}
  have hS : S.Nonempty := by
    obtain ⟨ω, h1, h2⟩ := exists_mem_sub_cj_ne_zero L
    obtain ⟨d, hd⟩ := hdisc ω h1
    exact ⟨d, ω, h1, h2, hd⟩
  obtain ⟨d, ⟨ω, hω, hω0, hd⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := 𝒪[F])).has_min S hS
  refine ⟨ω, hω, hω0, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_mul_of_anti L (y := x - L.cj x) (z := ω - L.cj ω)
    (by simp [L.cj_cj]) (by simp [L.cj_cj]) hω0
  by_cases hci : c ∈ 𝒪[F]
  · exact ⟨⟨c, hci⟩, hc⟩
  exfalso
  have hc0 : c ≠ 0 := by rintro rfl; exact hci (zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger 𝒪[F] c with ⟨c', rfl⟩ | ⟨c', hc'⟩
  · exact hci c'.2
  have hc'' : (c' : F) = c⁻¹ := hc'
  have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  have hx0 : x - L.cj x ≠ 0 := fun h => hω0 (by
    rw [hc] at h
    linear_combination algebraMap F E c⁻¹ * h - (ω - L.cj ω) * h1)
  obtain ⟨e, he⟩ := hdisc x hx
  refine hmin e ⟨x, hx, hx0, he⟩ ⟨?_, c' ^ 2, ?_, ?_⟩
  · rintro rfl
    exact hx0 (IsReduced.eq_zero _ ⟨2, by rw [he]; simp⟩)
  · intro hu
    obtain ⟨v, hv⟩ := ((isUnit_pow_iff two_ne_zero).1 hu).exists_right_inv
    have hv' : (c' : F) * v = 1 := congrArg Subtype.val hv
    rw [hc''] at hv'
    have : c = v := by field_simp at hv'; exact hv'.symm
    exact hci (this ▸ v.2)
  · apply Subtype.ext
    apply algebraMap_inj L
    rw [Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, ← hd, ← he, hc, hc'']
    linear_combination (-(ω - L.cj ω) ^ 2 * (algebraMap F E c * algebraMap F E c⁻¹ + 1)) * h1

theorem exists_sub_cj_mul_eq_one [CharZero F] (L : LocE F E) :
    ∃ ω ∈ L.O, ∃ e ∈ L.O, (ω - L.cj ω) * e = 1 := by
  obtain ⟨ω, hω, hω0, hgen⟩ := exists_generator L
  obtain ⟨t, ht⟩ := exists_trace L hω
  obtain ⟨n, hn⟩ := exists_norm L hω
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have hD : (ω - L.cj ω) ^ 2 = algebraMap F E (t ^ 2 - 4 * n : 𝒪[F]) := by
    push_cast
    have h4 : ((4 : 𝒪[F]) : F) = 4 := rfl
    simp only [h4, map_ofNat, ← ht, ← hn]
    ring
  by_cases hu : IsUnit (t ^ 2 - 4 * n)
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine ⟨ω, hω, (ω - L.cj ω) * algebraMap F E v,
      L.O.mul_mem (L.O.sub_mem hω (cj_mem L hω)) (hint v), ?_⟩
    rw [← mul_assoc, ← sq, hD, ← map_mul, ← Subring.coe_mul, hv]
    simp
  exfalso
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hm := hϖ.maximalIdeal_eq
  obtain ⟨a, ha1, ha2⟩ := exists_double_root (t := residue 𝒪[F] t) (n := residue 𝒪[F] n) (by
    have := (residue_eq_zero_iff _).2 (show t ^ 2 - 4 * n ∈ maximalIdeal 𝒪[F] from hu)
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using this)
  obtain ⟨a, rfl⟩ := residue_surjective a
  have h1 : ϖ ∣ t - 2 * a := by
    rw [← Ideal.mem_span_singleton, ← hm, ← residue_eq_zero_iff]
    simp only [map_sub, map_mul, map_ofNat, ha1, sub_self]
  have h2 : ϖ ∣ n - a ^ 2 := by
    rw [← Ideal.mem_span_singleton, ← hm, ← residue_eq_zero_iff]
    simp only [map_sub, map_pow, ha2, sub_self]
  obtain ⟨u, hu1⟩ := h1
  obtain ⟨v, hv1⟩ := h2
  have hu2 := congrArg (algebraMap 𝒪[F] E) hu1
  have hv2 := congrArg (algebraMap 𝒪[F] E) hv1
  simp only [map_sub, map_mul, map_pow, map_ofNat] at hu2 hv2
  have hal : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E a := fun _ => rfl
  simp only [hal, ← ht, ← hn] at hu2 hv2
  have hmem := L.unram ϖ hϖ (ω - algebraMap F E a) (L.O.sub_mem hω (hint a)) (by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨algebraMap F E u * ω - algebraMap F E v,
      L.O.sub_mem (L.O.mul_mem (hint u) hω) (hint v)⟩, ?_⟩
    show (algebraMap F E u * ω - algebraMap F E v) * algebraMap F E ϖ = _
    linear_combination (-ω) * hu2 + hv2)
  obtain ⟨⟨y, hy⟩, hy'⟩ := Submodule.mem_span_singleton.1 hmem
  have hy1 : y * algebraMap F E ϖ = ω - algebraMap F E a := hy'
  have hy2 := congrArg L.cj hy1
  simp only [map_mul, map_sub, AlgEquiv.commutes] at hy2
  obtain ⟨b, hb⟩ := hgen y hy
  have h3 : algebraMap F E (1 - ϖ * b : 𝒪[F]) * (ω - L.cj ω) = 0 := by
    push_cast
    linear_combination -hy1 + hy2 + algebraMap F E ϖ * hb
  have h4 : ((1 - ϖ * b : 𝒪[F]) : F) ≠ 0 := by
    intro h
    have h5 : 1 - ϖ * b = 0 := Subtype.ext h
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one b (sub_eq_zero.1 h5).symm)
  exact hω0 (((IsUnit.mk0 _ h4).map (algebraMap F E)).mul_right_eq_zero.1 h3)

end Local

theorem order_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ c : 𝒪[F], ∃ x ∈ L.O, x + L.cj x = algebraMap F E c) ∧ (∀ x ∈ L.O, L.cj x ∈ L.O ∧ (∃ c : 𝒪[F], x + L.cj x = algebraMap F E c) ∧ ∃ c : 𝒪[F], x * L.cj x = algebraMap F E c) ∧ (∀ x : E, (∀ b ∈ L.O, ∃ c : 𝒪[F], x * L.cj b + L.cj (x * L.cj b) = algebraMap F E c) → x ∈ L.O) ∧ IsPrincipalIdealRing L.O ∧ (∀ c : F, algebraMap F E c ∈ L.O ↔ c ∈ 𝒪[F]) ∧ (∀ j : ℕ, Nat.card (L.O ⧸ (Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)})) = resQ ϖ ^ (2 * j)) ∧ 2 ≤ resQ ϖ ∧ (∀ u : (𝒪[F])ˣ, ∃ x ∈ L.O, x * L.cj x = algebraMap F E ((u : 𝒪[F]) : F)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ
  obtain ⟨ω, hω, e, he, hωe⟩ := exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hal : ∀ a : 𝒪[F], ((algebraMap 𝒪[F] L.O a : L.O) : E) = algebraMap F E a := fun _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  have hbase : ∀ r, c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r := fun r =>
    Subtype.ext (by rw [hcv, hal, AlgEquiv.commutes])
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  have hu : IsUnit ((⟨ω, hω⟩ : L.O) - c ⟨ω, hω⟩) :=
    IsUnit.of_mul_eq_one ⟨e, he⟩ (Subtype.ext hωe)
  have hD : ∀ r : 𝒪[F], IsUnit (algebraMap 𝒪[F] L.O r) → IsUnit r := fun r hr => by
    obtain ⟨y, hy⟩ := hr.exists_right_inv
    have hy' := congrArg c hy
    rw [map_mul, hbase, map_one] at hy'
    obtain ⟨s, rfl⟩ := hfix y (by
      linear_combination y * hy' - c y * hy)
    exact IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hy, map_one]))
  have hH : HenselianRing 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[F]) := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hm := hϖ.maximalIdeal_eq
  refine ⟨fun a => ⟨algebraMap F E a * (ω * e), L.O.mul_mem (hint a) (L.O.mul_mem hω he), ?_⟩,
    fun x hx => ⟨cj_mem L hx, exists_trace L hx, exists_norm L hx⟩, fun x hx => ?_,
    isPrincipalIdealRing_of_henselian c hc hbase hfix hu hD, algebraMap_mem_iff L,
    fun j => ?_, ?_, fun u => ?_⟩
  · simp only [map_mul, AlgEquiv.commutes, hce]
    linear_combination algebraMap F E a * hωe
  · obtain ⟨s, hs⟩ := hx 1 L.O.one_mem
    obtain ⟨r, hr⟩ := hx ω hω
    simp only [map_mul, map_one, mul_one, L.cj_cj] at hs hr
    have : x = (algebraMap F E s * ω - algebraMap F E r) * e := by
      rw [← hs, ← hr]
      linear_combination (-x) * hωe
    rw [this]
    exact L.O.mul_mem (L.O.sub_mem (L.O.mul_mem (hint s) hω) (hint r)) he
  · have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {algebraMap 𝒪[F] L.O (ϖ ^ j)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff, hal, Subring.coe_pow]
    have hp : (Ideal.span {ϖ}).IsPrime := hm ▸ inferInstance
    have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
      (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := j)
    rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
    rw [hset, card_quot_eq_sq c hc hbase hinj hfix hu, hq, resQ, ← pow_mul, mul_comm]
  · rw [resQ, ← hm]
    have : Finite (IsLocalRing.ResidueField 𝒪[F]) := inferInstance
    exact Finite.one_lt_card (α := IsLocalRing.ResidueField 𝒪[F])
  · obtain ⟨x, hx⟩ := GlobalTheory.UnramifiedHermitian.exists_norm_eq_of_henselian (R₀ := 𝒪[F]) c hc hbase
      hfix ⟨_, hu⟩ (hbase u) (u.isUnit.map _)
    exact ⟨x, x.2, congrArg Subtype.val hx⟩

end GlobalTheory.UnramOrder
