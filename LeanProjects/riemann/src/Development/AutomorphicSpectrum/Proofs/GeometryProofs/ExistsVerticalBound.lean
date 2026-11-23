import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Vert

section Rings

variable {Ω : Type} [Field Ω]

def satQ (S : Subring Ω) : Subring Ω where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ S}
  mul_mem' := by
    rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have := S.mul_mem ha hb
    convert this using 1
    push_cast
    ring
  one_mem' := ⟨1, one_pos, by simpa using S.one_mem⟩
  add_mem' := by
    rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have := S.add_mem (S.mul_mem (natCast_mem S m) ha) (S.mul_mem (natCast_mem S n) hb)
    convert this using 1
    push_cast
    ring
  zero_mem' := ⟨1, one_pos, by simpa using S.zero_mem⟩
  neg_mem' := by
    rintro a ⟨n, hn, ha⟩
    exact ⟨n, hn, by simpa using S.neg_mem ha⟩

theorem mem_of_denominators (A : Subring Ω) (t : Ω)
    (H : ∀ M : Ideal A, M.IsMaximal → ∃ b : A, b ∉ M ∧ (b : Ω) * t ∈ A) : t ∈ A := by
  let D : Ideal A :=
    { carrier := {b | (b : Ω) * t ∈ A}
      add_mem' := by
        intro a b ha hb
        have := A.add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using A.zero_mem
      smul_mem' := by
        intro c b hb
        have := A.mul_mem c.2 hb
        simpa [mul_assoc] using this }
  by_contra ht
  have hD : D ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ D := h ▸ Submodule.mem_top
    have h2 : ((1 : A) : Ω) * t ∈ A := h1
    exact ht (by simpa using h2)
  obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal D hD
  obtain ⟨b, hb, hbt⟩ := H M hM
  exact hb (hDM hbt)

theorem natCast_notMem [CharZero Ω] (S : Subring Ω) (M : Ideal (satQ S)) (hM : M.IsMaximal) (n : ℕ) (hn : n ≠ 0) :
    (n : satQ S) ∉ M := by
  intro h
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hinv : (n : Ω)⁻¹ ∈ satQ S := ⟨n, Nat.pos_of_ne_zero hn, by
    rw [mul_inv_cancel₀ hn']
    exact S.one_mem⟩
  have hone : (1 : satQ S) = (⟨(n : Ω)⁻¹, hinv⟩ : satQ S) * (n : satQ S) := by
    apply Subtype.ext
    simp [hn']
  exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr (hone ▸ M.mul_mem_left _ h))

end Rings

theorem map_aeval_int {σ A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (π : A →+* B) (w : σ → A)
    (f : MvPolynomial σ ℤ) : π (aeval w f) = aeval (fun p => π (w p)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_chart (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g = aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  have h1 : ∏ p : Σ k, ι k, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [div_pow, Finset.prod_div_distrib]
  rw [h1, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [zpow_neg, zpow_natCast]

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h : (aeval (fun p : Σ k, ι k => C (y p) * X p.1) f : MvPolynomial K Ω) = 0 := RingHom.mem_ker.mp hf
  have e := map_aeval_int (eval fun _ : K => (1 : Ω)) (fun p : Σ k, ι k => (C (y p) * X p.1 : MvPolynomial K Ω)) f
  have e' : (fun p : Σ k, ι k => eval (fun _ : K => (1 : Ω)) (C (y p) * X p.1 : MvPolynomial K Ω)) = y := by
    funext p
    simp
  rw [e', h, map_zero] at e
  exact e.symm

theorem coord_ne_zero (y : (Σ k, ι k) → Ω) {p : Σ k, ι k} (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro hy
  apply h
  refine RingHom.mem_ker.mpr ?_
  simp [mConeMap, hy]

theorem charZero_of_horizontal (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hm : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap]
    refine RingHom.mem_ker.mpr ?_
    have e : ((n : MvPolynomial K Ω)) = C (n : Ω) := (map_natCast C n).symm
    simp [mConeMap, e, hn]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hm
  simpa using hm

theorem ne_zero_of_genUnit {y : (Σ k, ι k) → Ω} {d : ℕ} (hA : IsArithVar (mCoordIdeal y) d) {a : K → ℤ} {u : Ω}
    (H : GenUnit y a u) : u ≠ 0 := by
  obtain ⟨-, ⟨-, -, hR⟩, hH, -⟩ := hA
  haveI := charZero_of_horizontal y hH
  have hy : y ∈ ptsOver Ω (mCoordIdeal y) :=
    ⟨fun k => let ⟨i, hi⟩ := hR k; ⟨i, coord_ne_zero y hi⟩, fun f hf => aeval_eq_zero_of_mem y hf⟩
  obtain ⟨v, hv0, dg, dh, g, h, -, -, -, hgy, hhy, hgz⟩ := H Ω y hy
  intro hu
  rw [hu, zero_mul] at hgy
  rw [hgy] at hgz
  exact mul_ne_zero hv0 hhy hgz.symm

theorem exists_ratio (y : (Σ k, ι k) → Ω) (hS : IsMultiHomogIdeal (mCoordIdeal y)) {a : K → ℤ} {u : Ω}
    (H : GenUnit y a u) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {A : Subring Ω}
    (hx : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ A) (L : Type) [Field L] [CharZero L] (π : A →+* L) :
    ∃ b e : A, π b ≠ 0 ∧ π e ≠ 0 ∧ (e : Ω) = u * (∏ k, y ⟨k, c k⟩ ^ (-(a k))) * b := by
  let w : (Σ k, ι k) → A := fun p => ⟨y p / y ⟨p.1, c p.1⟩, hx p⟩
  have hval : ∀ f : MRing ι, ((aeval w f : A) : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) f :=
    fun f => map_aeval_int A.subtype w f
  obtain ⟨S, hS1, hS2⟩ := hS
  have hle : mCoordIdeal y ≤ RingHom.ker (aeval w : MRing ι →ₐ[ℤ] A) := by
    have hspan : Ideal.span S ≤ RingHom.ker (aeval w : MRing ι →ₐ[ℤ] A) := by
      refine Ideal.span_le.mpr fun f hf => ?_
      obtain ⟨d, hd⟩ := hS1 f hf
      have hfP : f ∈ mCoordIdeal y := hS2 ▸ Ideal.subset_span hf
      refine RingHom.mem_ker.mpr (Subtype.ext ?_)
      rw [hval, aeval_chart y c hd, aeval_eq_zero_of_mem y hfP]
      simp
    rwa [← hS2] at hspan
  let z : (Σ k, ι k) → L := fun p => π (w p)
  have hz : z ∈ ptsOver L (mCoordIdeal y) := by
    refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
    · have h1 : w ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
      simp [z, h1]
    · have h0 : (aeval w f : A) = 0 := RingHom.mem_ker.mp (hle hf)
      rw [← map_aeval_int π w f, h0, map_zero]
  obtain ⟨v, hv0, dg, dh, g, h, hg, hh, hd, hgy, hhz, hgz⟩ := H L z hz
  refine ⟨aeval w h, aeval w g, ?_, ?_, ?_⟩
  · rw [map_aeval_int]
    exact hhz
  · rw [map_aeval_int]
    show aeval z g ≠ 0
    rw [hgz]
    exact mul_ne_zero hv0 hhz
  · rw [hval, hval, aeval_chart y c hg, aeval_chart y c hh, hgy]
    have e : ∏ k, y ⟨k, c k⟩ ^ (-(dg k : ℤ)) =
        (∏ k, y ⟨k, c k⟩ ^ (-(a k))) * ∏ k, y ⟨k, c k⟩ ^ (-(dh k : ℤ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc k), hd k]
      congr 1
      ring
    rw [e]
    ring

theorem chart_mem (y : (Σ k, ι k) → Ω) (hS : IsMultiHomogIdeal (mCoordIdeal y)) [CharZero Ω] {a : K → ℤ} {u : Ω}
    (hu : u ≠ 0) (H : GenUnit y a u) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    u * (∏ k, y ⟨k, c k⟩ ^ (-(a k))) ∈ satQ (chartRingZ y c).toSubring ∧
      (u * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))⁻¹ ∈ satQ (chartRingZ y c).toSubring := by
  set S := (chartRingZ y c).toSubring with hSdef
  set t := u * ∏ k, y ⟨k, c k⟩ ^ (-(a k)) with ht
  have hx : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ satQ S := fun p =>
    ⟨1, one_pos, by
      have h : y p / y ⟨p.1, c p.1⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨p, rfl⟩
      simpa [hSdef] using h⟩
  have key : ∀ M : Ideal (satQ S), M.IsMaximal → ∃ b e : satQ S, b ∉ M ∧ e ∉ M ∧ (e : Ω) = t * b := by
    intro M hM
    letI := Ideal.Quotient.field M
    haveI : CharZero (satQ S ⧸ M) := charZero_of_inj_zero fun n hn => by
      by_contra h0
      apply natCast_notMem S M hM n h0
      have h1 : Ideal.Quotient.mk M (n : satQ S) = 0 := by
        rw [map_natCast]
        exact hn
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    obtain ⟨b, e, hb, he, hbe⟩ := exists_ratio y hS H c hc hx (satQ S ⧸ M) (Ideal.Quotient.mk M)
    exact ⟨b, e, fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mpr h),
      fun h => he (Ideal.Quotient.eq_zero_iff_mem.mpr h), hbe⟩
  have ht0 : t ≠ 0 := mul_ne_zero hu (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  constructor
  · refine mem_of_denominators _ _ fun M hM => ?_
    obtain ⟨b, e, hb, -, hbe⟩ := key M hM
    refine ⟨b, hb, ?_⟩
    rw [mul_comm, ← hbe]
    exact e.2
  · refine mem_of_denominators _ _ fun M hM => ?_
    obtain ⟨b, e, -, he, hbe⟩ := key M hM
    refine ⟨e, he, ?_⟩
    rw [hbe, mul_comm t, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    exact b.2

theorem mem_chartLatNm_one {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω}
    (hs : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)) ∈ chartRingZ y c) :
    s ∈ chartLatNm y a 1 := by
  intro c hc
  have h := hs c hc
  simp only [Nat.cast_one, one_mul]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

end Charts

theorem exists_vertBound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y →
    ∀ (a : K → ℤ) (u : Ω), GenUnit y a u → ∃ c : ℝ, VertBound y a u c := by
  intro K _ ι _ Ω _ y d hA _ a u H
  classical
  have hu := ne_zero_of_genUnit hA H
  obtain ⟨-, ⟨-, hS, -⟩, hH, -⟩ := hA
  haveI := charZero_of_horizontal y hH
  have hn : ∀ c : ∀ k, ι k, ∃ n : ℕ, 0 < n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (u * ∏ k, y ⟨k, c k⟩ ^ (-(a k))) ∈ chartRingZ y c ∧
      (n : Ω) * (u * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))⁻¹ ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨⟨n₁, p₁, h₁⟩, ⟨n₂, p₂, h₂⟩⟩ := chart_mem y hS hu H c hc
      refine ⟨n₁ * n₂, Nat.mul_pos p₁ p₂, fun _ => ⟨?_, ?_⟩⟩
      · have h := (chartRingZ y c).mul_mem (natCast_mem (chartRingZ y c) n₂) h₁
        convert h using 1
        push_cast
        ring
      · have h := (chartRingZ y c).mul_mem (natCast_mem (chartRingZ y c) n₁) h₂
        convert h using 1
        push_cast
        ring
    · exact ⟨1, one_pos, fun h => absurd h hc⟩
  choose n hn0 hn using hn
  have hm0 : 0 < ∏ c, n c := Finset.prod_pos fun c _ => hn0 c
  have hdiv : ∀ c, ∃ r : ℕ, ∏ c, n c = n c * r := fun c => Finset.dvd_prod_of_mem n (Finset.mem_univ c)
  refine ⟨Real.log (∏ c, n c : ℕ), hu, 1, ∏ c, n c, one_pos, hm0, by simp, ?_, ?_⟩
  · refine mem_chartLatNm_one fun c hc => ?_
    obtain ⟨r, hr⟩ := hdiv c
    have h := (chartRingZ y c).mul_mem (natCast_mem (chartRingZ y c) r) (hn c hc).1
    rw [hr]
    convert h using 1
    push_cast
    ring
  · refine mem_chartLatNm_one fun c hc => ?_
    obtain ⟨r, hr⟩ := hdiv c
    have h := (chartRingZ y c).mul_mem (natCast_mem (chartRingZ y c) r) (hn c hc).2
    rw [hr]
    convert h using 1
    have e : ∏ k, y ⟨k, c k⟩ ^ (-((-a) k)) = (∏ k, y ⟨k, c k⟩ ^ (-(a k)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [zpow_neg]
    rw [e, mul_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ar.Vert
