import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

section Factor

variable {R : Type} [CommRing R] {e : R}

local notation "Q" e:max => Ideal.Quotient.mk (Ideal.span {1 - e})

private theorem mk_eq_iff (he : IsIdempotentElem e) (a b : R) :
    (Q e) a = (Q e) b ↔ e * a = e * b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    linear_combination e * hc - c * he.eq
  · intro h
    exact ⟨a - b, by linear_combination h⟩

private theorem mk_self (he : IsIdempotentElem e) : (Q e) e = 1 := by
  rw [← map_one (Q e), mk_eq_iff he, mul_one, he.eq]

private theorem dvd_of_mk_dvd (he : IsIdempotentElem e) {a b : R} (h : (Q e) a ∣ (Q e) b) : a ∣ e * b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, mk_eq_iff he] at hc
  exact ⟨e * c, by linear_combination hc⟩

private theorem mem_pow_iff {S : Type} [CommRing S] (a x : S) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule S S) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem perfect_quot (he : IsIdempotentElem e) {p : ℕ} (hp : 0 < p) [PerfectRing R p] :
    PerfectRing (R ⧸ Ideal.span {1 - e}) p := by
  have hep : e ^ p = e := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    exact he.pow_succ_eq k
  have hb := PerfectRing.bijective_frobenius (R := R) (p := p)
  refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h' : (Q e) (a ^ p) = (Q e) (b ^ p) := by simpa only [map_pow] using h
    rw [mk_eq_iff he] at h' ⊢
    apply hb.1
    show (e * a) ^ p = (e * b) ^ p
    rw [mul_pow, mul_pow, hep, h']
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, hb'⟩ := hb.2 a
    exact ⟨(Q e) b, by rw [← hb']; simp only [map_pow]⟩

private theorem nzd_quot (he : IsIdempotentElem e) {π : R} (h : π ∈ nonZeroDivisors R) :
    (Q e) π ∈ nonZeroDivisors (R ⧸ Ideal.span {1 - e}) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, ← map_zero (Q e), mk_eq_iff he, mul_zero] at hx
  rw [← map_zero (Q e), mk_eq_iff he, mul_zero]
  rw [mem_nonZeroDivisors_iff_right] at h
  exact h _ (by linear_combination hx)

private theorem complete_quot (he : IsIdempotentElem e) {π : R} (h : IsAdicComplete (Ideal.span {π}) R) :
    IsAdicComplete (Ideal.span {(Q e) π}) (R ⧸ Ideal.span {1 - e}) := by
  have hH := h.toIsHausdorff
  have hP := h.toIsPrecomplete
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_zero (Q e), mk_eq_iff he, mul_zero]
    refine hH.haus' _ fun n => ?_
    rw [SModEq.zero, mem_pow_iff]
    have := (hx n)
    rw [SModEq.zero, mem_pow_iff, ← map_pow] at this
    exact dvd_of_mk_dvd he this
  · choose g hg using fun n => Ideal.Quotient.mk_surjective (f n)
    obtain ⟨L, hL⟩ := hP.prec' (fun n => e * g n) (fun {m n} hmn => by
      have := hf hmn
      rw [SModEq.sub_mem, mem_pow_iff, ← map_pow, ← hg m, ← hg n, ← map_sub] at this
      rw [SModEq.sub_mem, mem_pow_iff]
      have h2 := dvd_of_mk_dvd he this
      rwa [mul_sub] at h2)
    refine ⟨(Q e) L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, mem_pow_iff] at this ⊢
    have h3 := map_dvd (Q e) this
    rw [map_pow, map_sub, map_mul, mk_self he, one_mul, hg n] at h3
    exact h3

private theorem aic_quot (I : Ideal R) (h : ∀ P : R[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x) :
    ∀ P : (R ⧸ I)[X], P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x := by
  intro P hP hd
  have hl : P ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective P)
  obtain ⟨q, rfl, hdeg, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
  obtain ⟨x, hx⟩ := h q hq (hdeg ▸ hd)
  exact ⟨_, hx.map⟩

private theorem val_quot (he : IsIdempotentElem e) {π : R}
    (h : ∀ f g : R, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f}) :
    ∀ f g : R ⧸ Ideal.span {1 - e}, (∃ N : ℕ, (Q e) π ^ N ∈ Ideal.span {f, g}) →
      ∃ u : R ⧸ Ideal.span {1 - e}, IsIdempotentElem u ∧ u * f ∈ Ideal.span {g} ∧ (1 - u) * g ∈ Ideal.span {f} := by
  intro f g ⟨N, hN⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨c', d', hcd⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d'
  have hE : e * (c * a + d * b) = e * π ^ N := by
    rw [← mk_eq_iff he]
    simpa only [map_add, map_mul, map_pow] using hcd
  obtain ⟨u, hu, h1, h2⟩ := h (a * e + (1 - e)) (b * e) ⟨N, Ideal.mem_span_pair.2
    ⟨c * e + π ^ N * (1 - e), d, by
      linear_combination hE + (c * a - c - π ^ N * a + π ^ N) * he.eq⟩⟩
  have hm : (Q e) (1 - e) = 0 := by rw [map_sub, map_one, mk_self he, sub_self]
  have ha : (Q e) (a * e + (1 - e)) = (Q e) a := by
    rw [map_add, map_mul, mk_self he, hm, mul_one, add_zero]
  have hb : (Q e) (b * e) = (Q e) b := by rw [map_mul, mk_self he, mul_one]
  rw [Ideal.mem_span_singleton] at h1 h2
  refine ⟨(Q e) u, ?_, ?_, ?_⟩
  · show (Q e) u * (Q e) u = (Q e) u
    rw [← map_mul, hu.eq]
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (Q e) h1
    rwa [hb, map_mul, ha] at this
  · rw [Ideal.mem_span_singleton]
    have := map_dvd (Q e) h2
    rwa [ha, map_mul, hb, map_sub, map_one] at this

end Factor

variable {l : ℕ} [Fact l.Prime]

private def factor (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) : PAlg l where
  A := A.A ⧸ Ideal.span {1 - e}
  s := (Ideal.Quotient.mk _).comp A.s
  perf := perfect_quot he (Fact.out : l.Prime).pos
  compl := complete_quot he A.compl
  tf := nzd_quot he A.tf

private theorem factor_isTest (A : PAlg l) {e : A.A} (he : IsIdempotentElem e) (h : A.IsTest) :
    (factor A he).IsTest :=
  ⟨aic_quot _ h.1, val_quot he h.2⟩

theorem decEx : DecEx := by
  intro l _ A ι _ e he
  refine ⟨fun i => ⟨factor A.obj (he.idem i), factor_isTest _ _ A.property⟩,
    fun i => ObjectProperty.homMk ⟨Ideal.Quotient.mk _, rfl⟩, ?_, fun i => ?_⟩
  · exact he.bijective_pi
  · exact mk_self (he.idem i)

end UpperTheory.Ru.crystallineComparison
