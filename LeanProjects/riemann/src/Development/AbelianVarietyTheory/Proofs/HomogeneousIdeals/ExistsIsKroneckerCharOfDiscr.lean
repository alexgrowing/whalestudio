import Mathlib

open NumberField Module
open scoped NumberTheorySymbols

namespace GlobalTheory.QuadraticZeta

section Ring

variable {R : Type*} [CommRing R]

theorem eq_coord (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x : R) :
    x = (b.repr x 0 : R) + (b.repr x 1 : R) * b 1 := by
  conv_lhs => rw [← b.sum_repr x]
  simp [h0]

theorem repr_coord (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) (x y : ℤ) :
    b.repr (x + y * b 1) 0 = x ∧ b.repr (x + y * b 1) 1 = y := by
  have : (x + y * b 1 : R) = x • b 0 + y • b 1 := by simp [h0]
  rw [this]
  simp [-zsmul_eq_mul]

theorem discr_eq (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n) :
    Algebra.discr ℤ b = t ^ 2 - 4 * n := by
  have tr : ∀ x y : ℤ, Algebra.trace ℤ R (x + y * b 1) = 2 * x + y * t := by
    intro x y
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, h0, mul_one, (repr_coord b h0 x y).1,
      show (x + y * b 1 : R) * b 1 = (-(y * n) : ℤ) + (x + y * t : ℤ) * b 1 by
        push_cast; linear_combination (y : R) * hw, (repr_coord b h0 _ _).2]
    ring
  have t1 := tr 1 0
  have t2 := tr 0 1
  have t3 := tr (-n) t
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h0, mul_one, one_mul]
  rw [show b 1 * b 1 = (-n : ℤ) + t * b 1 by push_cast; linear_combination hw, t3]
  simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero, one_mul, zero_add] at t1 t2
  rw [t1, t2]
  ring

theorem exists_ringHom (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ}
    (hw : b 1 ^ 2 = t * b 1 - n) {S : Type*} [CommRing S] {β : S} (hβ : β ^ 2 = t * β - n) :
    ∃ φ : R →+* S, φ (b 1) = β := by
  let f : R →ₗ[ℤ] S := b.constr ℤ ![1, β]
  have hf : ∀ x y : ℤ, f (x + y * b 1) = x + y * β := by
    intro x y
    have : (x + y * b 1 : R) = x • b 0 + y • b 1 := by simp [h0]
    rw [this]
    rw [map_add, map_smul, map_smul]
    simp [f]
  refine ⟨(AlgHom.ofLinearMap f (by simpa using hf 1 0) fun x y => ?_).toRingHom,
    by simpa using hf 0 1⟩
  rw [eq_coord b h0 x, eq_coord b h0 y]
  generalize b.repr x 0 = x0, b.repr x 1 = x1, b.repr y 0 = y0, b.repr y 1 = y1
  rw [show (x0 + x1 * b 1 : R) * (y0 + y1 * b 1) = (x0 * y0 - x1 * y1 * n : ℤ)
      + (x0 * y1 + x1 * y0 + x1 * y1 * t : ℤ) * b 1 by
    push_cast; linear_combination (x1 * y1 : R) * hw, hf, hf, hf]
  push_cast
  linear_combination (-(x1 * y1) : S) * hβ

end Ring

variable {K : Type*} [Field K] [NumberField K]

theorem exists_basis (h2 : finrank ℚ K = 2) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t n : ℤ), b 0 = 1 ∧ b 1 ^ 2 = t * b 1 - n ∧
      discr K = t ^ 2 - 4 * n := by
  let e : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans h2)
  have h1 : (1 : 𝓞 K) = e.repr 1 0 • e 0 + e.repr 1 1 • e 1 := by
    conv_lhs => rw [← e.sum_repr 1]
    simp
  generalize e.repr 1 0 = x, e.repr 1 1 = y at h1
  have hc : IsCoprime x y := by
    refine isCoprime_of_dvd x y (fun h => by simp [h.1, h.2] at h1) ?_
    rintro z hz - ⟨x', rfl⟩ ⟨y', rfl⟩
    apply hz
    have hu : IsUnit (algebraMap ℤ (𝓞 K) z) :=
      IsUnit.of_mul_eq_one (x' • e 0 + y' • e 1) (by rw [h1]; simp; ring)
    have := hu.map (Algebra.norm ℤ)
    rw [Algebra.norm_algebraMap_of_basis e] at this
    exact (isUnit_pow_iff (by simp)).1 this
  obtain ⟨u, v, huv⟩ := hc
  have hd : IsUnit (e.det ![x • e 0 + y • e 1, -v • e 0 + u • e 1]) := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply]
    simp [-zsmul_eq_mul]
    convert isUnit_one using 1
    linarith
  obtain ⟨hi, hs⟩ := (e.is_basis_iff_det).2 hd
  let b : Basis (Fin 2) ℤ (𝓞 K) := Basis.mk hi hs.ge
  have h0 : b 0 = 1 := by simp [b, h1.symm, -zsmul_eq_mul]
  have hw : b 1 ^ 2 = (b.repr (b 1 ^ 2) 1 : ℤ) * b 1 - (-b.repr (b 1 ^ 2) 0 : ℤ) := by
    conv_lhs => rw [eq_coord b h0 (b 1 ^ 2)]
    push_cast
    ring
  exact ⟨b, _, _, h0, hw, by rw [← discr_eq_discr K b, discr_eq b h0 hw]⟩

def kroneckerAt (D : ℤ) (p : ℕ) : ℤ := if p = 2 then ZMod.χ₈ (D : ZMod 8) else J(D | p)

theorem roots_cases (t n : ℤ) {p : ℕ} (hp : p.Prime) :
    (kroneckerAt (t ^ 2 - 4 * n) p = -1 ∧ ∀ β : ZMod p, β ^ 2 ≠ t * β - n) ∨
    ∃ β β' : ZMod p, β + β' = t ∧ β * β' = n ∧
      ((kroneckerAt (t ^ 2 - 4 * n) p = 0 ∧ β = β') ∨
        (kroneckerAt (t ^ 2 - 4 * n) p = 1 ∧ β ≠ β')) := by
  rcases eq_or_ne p 2 with rfl | h2
  · simp only [kroneckerAt, if_true]
    have key : ∀ t n : ZMod 8,
        (ZMod.χ₈ (t ^ 2 - 4 * n) = -1 ∧ ∀ β : ZMod 2, β ^ 2 ≠ t.cast * β - n.cast) ∨
        ∃ β β' : ZMod 2, β + β' = t.cast ∧ β * β' = n.cast ∧
          ((ZMod.χ₈ (t ^ 2 - 4 * n) = 0 ∧ β = β') ∨ (ZMod.χ₈ (t ^ 2 - 4 * n) = 1 ∧ β ≠ β')) := by
      decide
    have := key t n
    rw [ZMod.cast_intCast (by norm_num), ZMod.cast_intCast (by norm_num)] at this
    push_cast
    exact this
  · haveI := Fact.mk hp
    have h2' : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    simp only [kroneckerAt, if_neg h2, ← jacobiSym.legendreSym.to_jacobiSym]
    by_cases hs : IsSquare ((t ^ 2 - 4 * n : ℤ) : ZMod p)
    · obtain ⟨r, hr⟩ := hs
      refine Or.inr ⟨(t + r) / 2, (t - r) / 2, by field_simp; ring, ?_, ?_⟩
      · push_cast at hr
        field_simp
        linear_combination hr
      · by_cases h0 : r = 0
        · exact Or.inl ⟨(legendreSym.eq_zero_iff _ _).2 (by simp [hr, h0]), by simp [h0]⟩
        · refine Or.inr ⟨(legendreSym.eq_one_iff _ (by simp [hr, h0])).2 ⟨r, hr⟩, fun h => h0 ?_⟩
          field_simp at h
          exact mul_left_cancel₀ h2' (by linear_combination h)
    · refine Or.inl ⟨(legendreSym.eq_neg_one_iff _).2 hs, fun β h => hs ⟨2 * β - t, ?_⟩⟩
      push_cast
      linear_combination (-4) * h

noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard

theorem ncard_dvd {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) (k : ℕ) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = k ∧ J ∣ I}.ncard
      = if Ideal.absNorm J ∣ k then idealCount K (k / Ideal.absNorm J) else 0 := by
  have hN : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ hN, idealCount, ← Set.ncard_image_of_injective
      {I | Ideal.absNorm I = m} (mul_right_injective₀ (show J ≠ 0 from hJ))]
    congr 1
    ext I
    constructor
    · rintro ⟨h1, I', rfl⟩
      rw [map_mul] at h1
      exact ⟨I', Nat.eq_of_mul_eq_mul_left hN h1, rfl⟩
    · rintro ⟨I', h1, rfl⟩
      exact ⟨by rw [map_mul, h1], dvd_mul_right _ _⟩
  · convert Set.ncard_empty (Ideal (𝓞 K))
    ext I
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl h'
    exact h (map_dvd _ h')

theorem int_dvd_of_mem {p : ℕ} {P : Ideal (𝓞 K)} (hP : P.under ℤ = .span {(p : ℤ)}) (x : ℤ) :
    (x : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ x := by
  rw [← Ideal.mem_span_singleton, ← hP, Ideal.under, Ideal.mem_comap]
  simp

theorem absNorm_ker {p : ℕ} (φ : 𝓞 K →+* ZMod p) : Ideal.absNorm (RingHom.ker φ) = p := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv,
    Nat.card_zmod]

section

variable (b : Basis (Fin 2) ℤ (𝓞 K)) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n)
  {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hPm : P.IsMaximal)
  (hP : P.under ℤ = .span {(p : ℤ)})
include h0 hw hp hPm hP

theorem eq_span_of_no_root (h : ∀ β : ZMod p, β ^ 2 ≠ t * β - n) :
    P = Ideal.span {(p : 𝓞 K)} := by
  refine le_antisymm (fun z hz => ?_) ?_
  · rw [eq_coord b h0 z] at hz ⊢
    generalize b.repr z 0 = x, b.repr z 1 = y at hz ⊢
    have h1 : ((x ^ 2 + t * x * y + n * y ^ 2 : ℤ) : 𝓞 K) ∈ P := by
      convert P.mul_mem_left (x + y * (t - b 1)) hz using 1
      push_cast
      linear_combination (y : 𝓞 K) ^ 2 * hw
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    push_cast at h1
    haveI := Fact.mk hp
    have hy : (y : ZMod p) = 0 := by
      by_contra hy
      refine h (-x / y) ?_
      field_simp
      linear_combination h1
    have hx : (x : ZMod p) = 0 := by simpa [hy] using h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact Ideal.mem_span_singleton.2 ⟨x + y * b 1, by push_cast; ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact_mod_cast (int_dvd_of_mem hP p).2 dvd_rfl

omit hw in
theorem eq_ker_of_mem (φ : 𝓞 K →+* ZMod p) {c : ℤ} (hc : φ (b 1) = c) (hm : b 1 - c ∈ P) :
    P = RingHom.ker φ := by
  haveI := Fact.mk hp
  refine ((RingHom.ker_isMaximal_of_surjective φ (ZMod.ringHom_surjective φ)).eq_of_le
    hPm.ne_top fun z hz => ?_).symm
  rw [eq_coord b h0 z] at hz ⊢
  generalize b.repr z 0 = x, b.repr z 1 = y at hz ⊢
  have h1 : ((x + y * c : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [hc] using hz
  convert P.add_mem h1 (P.mul_mem_left y hm) using 1
  push_cast
  ring

theorem eq_ker_or (φ φ' : 𝓞 K →+* ZMod p) (h1 : φ (b 1) + φ' (b 1) = t)
    (h2 : φ (b 1) * φ' (b 1) = n) : P = RingHom.ker φ ∨ P = RingHom.ker φ' := by
  obtain ⟨c, hc⟩ := ZMod.intCast_surjective (φ (b 1))
  obtain ⟨c', hc'⟩ := ZMod.intCast_surjective (φ' (b 1))
  have e1 : ((c + c' - t : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc, hc', h1, sub_self]
  have e2 : ((c * c' - n : ℤ) : 𝓞 K) ∈ P := by
    rw [int_dvd_of_mem hP, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hc, hc', h2, sub_self]
  have : (b 1 - c) * (b 1 - c') ∈ P := by
    convert P.sub_mem e2 (P.mul_mem_left (b 1) e1) using 1
    push_cast
    linear_combination hw
  rcases hPm.isPrime.mem_or_mem this with h | h
  · exact Or.inl (eq_ker_of_mem b h0 hp hPm hP φ hc.symm h)
  · exact Or.inr (eq_ker_of_mem b h0 hp hPm hP φ' hc'.symm h)

end

theorem idealCount_prime_mul (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (idealCount K (p * m) : ℤ) = (1 + kroneckerAt (discr K) p) * idealCount K m
      - kroneckerAt (discr K) p * if p ∣ m then (idealCount K (m / p) : ℤ) else 0 := by
  obtain ⟨b, t, n, h0, hw, hD⟩ := exists_basis h2
  haveI := Fact.mk hp
  have hex : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = p * m →
      ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.under ℤ = .span {(p : ℤ)} ∧ P ∣ I := fun I hI =>
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I (hI ▸ dvd_mul_right _ _)
  have hsq : ∀ J : Ideal (𝓞 K), Ideal.absNorm J = p * p →
      {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ J ∣ I}.ncard
        = if p ∣ m then idealCount K (m / p) else 0 := fun J hJ => by
    rw [ncard_dvd (by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hJ]; simp [hp.ne_zero]), hJ,
      Nat.mul_div_mul_left _ _ hp.pos]
    simp only [Nat.mul_dvd_mul_iff_left hp.pos]
  have hone : ∀ J : Ideal (𝓞 K), Ideal.absNorm J = p →
      {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ J ∣ I}.ncard = idealCount K m := fun J hJ => by
    rw [ncard_dvd (by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hJ]; simp [hp.ne_zero]), hJ,
      Nat.mul_div_cancel_left _ hp.pos, if_pos (dvd_mul_right _ _)]
  rw [hD]
  rcases roots_cases t n hp with ⟨hκ, h⟩ | ⟨β, β', hs, hm, h⟩
  · have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p * p := by
      rw [Ideal.absNorm_span_singleton, show (p : 𝓞 K) = algebraMap ℤ _ p by simp,
        Algebra.norm_algebraMap_of_basis b]
      simp [sq, Int.natAbs_mul]
    have := hsq _ hN
    rw [hκ, idealCount, show {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m}
      = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ Ideal.span {(p : 𝓞 K)} ∣ I} from
      Set.ext fun I => (and_iff_left_of_imp fun hI => by
        obtain ⟨P, h1, h2, h3⟩ := hex I hI
        exact eq_span_of_no_root b h0 hw hp h1 h2 h ▸ h3).symm, this]
    split_ifs <;> simp
  · obtain ⟨φ, hφ⟩ := exists_ringHom b h0 hw (β := β) (by rw [← hs, ← hm]; ring)
    obtain ⟨φ', hφ'⟩ := exists_ringHom b h0 hw (β := β') (by rw [← hs, ← hm]; ring)
    rcases h with ⟨hκ, rfl⟩ | ⟨hκ, hne⟩
    · rw [hκ, idealCount, show {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m}
        = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} from
        Set.ext fun I => (and_iff_left_of_imp fun hI => by
          obtain ⟨P, h1, h2, h3⟩ := hex I hI
          exact (or_self_iff.1 (eq_ker_or b h0 hw hp h1 h2 φ φ (by rw [hφ, hs])
            (by rw [hφ, hm]))) ▸ h3).symm, hone _ (absNorm_ker φ)]
      simp
    · have hmax := RingHom.ker_isMaximal_of_surjective φ (ZMod.ringHom_surjective φ)
      have hmax' := RingHom.ker_isMaximal_of_surjective φ' (ZMod.ringHom_surjective φ')
      have hk : RingHom.ker φ ≠ RingHom.ker φ' := fun e => by
        obtain ⟨c, hc⟩ := ZMod.intCast_surjective β
        have : b 1 - c ∈ RingHom.ker φ := by simp [RingHom.mem_ker, hφ, hc]
        rw [e] at this
        exact hne (by simpa [RingHom.mem_ker, hφ', hc, sub_eq_zero, eq_comm] using this)
      have hcop : IsCoprime (RingHom.ker φ) (RingHom.ker φ') :=
        Ideal.isCoprime_iff_sup_eq.2 (hmax.coprime_of_ne hmax' hk)
      have hfin := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (p * m)
      have hu := Set.ncard_union_add_ncard_inter
        {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I}
        {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
        (hfin.subset fun _ h => h.1) (hfin.subset fun _ h => h.1)
      have e1 : {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} ∪
          {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
          = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m} := by
        ext I
        refine ⟨fun h => h.elim And.left And.left, fun hI => ?_⟩
        obtain ⟨P, h1, h2, h3⟩ := hex I hI
        rcases eq_ker_or b h0 hw hp h1 h2 φ φ' (by rw [hφ, hφ', hs]) (by rw [hφ, hφ', hm])
          with rfl | rfl
        exacts [Or.inl ⟨hI, h3⟩, Or.inr ⟨hI, h3⟩]
      have e2 : {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ ∣ I} ∩
          {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ' ∣ I}
          = {I : Ideal (𝓞 K) | Ideal.absNorm I = p * m ∧ RingHom.ker φ * RingHom.ker φ' ∣ I} := by
        ext I
        exact ⟨fun h => ⟨h.1.1, hcop.mul_dvd h.1.2 h.2.2⟩, fun h =>
          ⟨⟨h.1, (dvd_mul_right _ _).trans h.2⟩, h.1, (dvd_mul_left _ _).trans h.2⟩⟩
      rw [e1, e2, hone _ (absNorm_ker φ), hone _ (absNorm_ker φ'),
        hsq _ (by rw [map_mul, absNorm_ker, absNorm_ker])] at hu
      rw [hκ, idealCount]
      have hu' := congrArg (Nat.cast : ℕ → ℤ) hu
      push_cast at hu'
      linarith

theorem sum_divisors_prime_mul {R : Type*} [CommRing R] (χ : ℕ → R)
    (hχ : ∀ a b, χ (a * b) = χ a * χ b) {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    ∑ e ∈ (p * m).divisors, χ e = (1 + χ p) * ∑ e ∈ m.divisors, χ e
      - χ p * if p ∣ m then ∑ e ∈ (m / p).divisors, χ e else 0 := by
  have key : ∀ k, k ≠ 0 → ∑ e ∈ (p * k).divisors with p ∣ e, χ e
      = χ p * ∑ e ∈ k.divisors, χ e := by
    intro k hk
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun e _ => p * e) ?_ ?_ ?_ fun e _ => (hχ _ _).symm
    · intro e he
      simp only [Nat.mem_divisors, Finset.mem_filter] at he ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left _ he.1, mul_ne_zero hp.ne_zero hk⟩, dvd_mul_right _ _⟩
    · intro e _ e' _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro e he
      simp only [Nat.mem_divisors, Finset.mem_filter] at he
      obtain ⟨⟨h1, -⟩, e, rfl⟩ := he
      exact ⟨e, Nat.mem_divisors.2 ⟨(Nat.mul_dvd_mul_iff_left hp.pos).1 h1, hk⟩, rfl⟩
  have e1 : ((p * m).divisors.filter fun e => ¬ p ∣ e) = m.divisors.filter fun e => ¬ p ∣ e := by
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter]
    refine ⟨fun h => ⟨⟨?_, hm⟩, h.2⟩, fun h => ⟨⟨h.1.1.mul_left _, mul_ne_zero hp.ne_zero hm⟩, h.2⟩⟩
    exact ((hp.coprime_iff_not_dvd.2 h.2).symm.dvd_mul_left).1 h.1.1
  have e2 : ∑ e ∈ m.divisors with p ∣ e, χ e
      = χ p * if p ∣ m then ∑ e ∈ (m / p).divisors, χ e else 0 := by
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [key k (right_ne_zero_of_mul hm), Nat.mul_div_cancel_left _ hp.pos]
    · rw [mul_zero]
      refine Finset.sum_eq_zero fun e he => ?_
      simp only [Nat.mem_divisors, Finset.mem_filter] at he
      exact absurd (he.2.trans he.1.1) h
  have e3 := Finset.sum_filter_add_sum_filter_not m.divisors (fun e => p ∣ e) χ
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun e => p ∣ e), key m hm, e1, ← e2]
  linear_combination e3

theorem idealCount_eq_sum (h2 : finrank ℚ K = 2) {R : Type*} [CommRing R] (χ : ℕ → R)
    (h1 : χ 1 = 1) (hχ : ∀ a b, χ (a * b) = χ a * χ b)
    (hκ : ∀ p : ℕ, p.Prime → χ p = kroneckerAt (discr K) p) {m : ℕ} (hm : m ≠ 0) :
    (idealCount K m : R) = ∑ e ∈ m.divisors, χ e := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [idealCount, Ideal.absNorm_eq_one_iff, h1]
    obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd hm1
    have hk : k ≠ 0 := right_ne_zero_of_mul hm
    have hlt : k < p * k := lt_mul_left (Nat.pos_of_ne_zero hk) hp.one_lt
    have := congrArg (Int.cast : ℤ → R) (idealCount_prime_mul h2 hp k)
    push_cast at this
    rw [this, sum_divisors_prime_mul χ hχ hp hk, hκ p hp, ih k hlt hk]
    congr 2
    split_ifs with h
    · exact ih _ ((Nat.div_le_self _ _).trans_lt hlt)
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h) hp.pos).ne'
    · rfl

theorem discr_mod_four (h2 : finrank ℚ K = 2) : discr K % 4 = 0 ∨ discr K % 4 = 1 := by
  obtain ⟨-, t, n, -, -, hD⟩ := exists_basis h2
  rcases Int.even_or_odd' t with ⟨k, rfl | rfl⟩
  · left
    rw [hD, show (2 * k) ^ 2 - 4 * n = 4 * (k ^ 2 - n) by ring, Int.mul_emod_right]
  · right
    rw [hD, show (2 * k + 1) ^ 2 - 4 * n = 1 + 4 * (k ^ 2 + k - n) by ring, Int.add_mul_emod_self_left]
    rfl

end GlobalTheory.QuadraticZeta

namespace GlobalTheory

open QuadraticZeta

def IsKroneckerChar {d : ℕ} (χ : DirichletCharacter ℂ d) : Prop :=
  ∀ n : ℕ, Odd n → χ n = (J(-(d : ℤ) | n) : ℤ)

namespace IsKroneckerChar

variable {d : ℕ} {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
include hχ

theorem apply_two (h4 : d % 4 ≠ 1) : χ 2 = (ZMod.χ₈ ((-(d : ℤ) : ℤ) : ZMod 8) : ℤ) := by
  rcases Nat.even_or_odd d with h | h
  · rw [MulChar.map_nonunit, (ZMod.χ₈_int_eq_if_mod_eight _),
      if_pos (by obtain ⟨k, rfl⟩ := h; omega)]
    · simp
    · rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by simp, ZMod.isUnit_iff_coprime,
        Nat.coprime_two_left, Nat.not_odd_iff_even]
      exact h
  · have h' : Odd (d + 2) := h.add_even even_two
    have := hχ _ h'
    rw [jacobiSym.mod_left' (a₂ := 2) (by
      push_cast
      rw [show (2 : ℤ) = -d + (d + 2) by ring, show (d : ℤ) + (-d + (d + 2)) = d + 2 by ring,
        Int.add_emod_right]), jacobiSym.at_two h'] at this
    rw [Nat.odd_iff] at h
    rw [show (2 : ZMod d) = ((d + 2 : ℕ) : ZMod d) by simp, this, ZMod.χ₈_int_eq_if_mod_eight,
      ZMod.χ₈_nat_eq_if_mod_eight]
    congr 1
    split_ifs <;> omega

theorem apply_neg_one (hd : 0 < d) : χ (-1) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h' : Odd (4 * k + 3) := ⟨2 * k + 1, by ring⟩
  have := hχ _ h'
  rw [← one_mul J(_ | _), ← jacobiSym.at_four h', ← jacobiSym.mul_left,
    jacobiSym.mod_left' (a₂ := -1) (by
      push_cast
      rw [show (4 : ℤ) * -(k + 1) = -1 - (4 * k + 3) by ring, Int.sub_emod_right]),
    jacobiSym.at_neg_one h', ZMod.χ₄_nat_three_mod_four (by omega)] at this
  have e : ((4 * k + 3 : ℕ) : ZMod (k + 1)) = -1 := by
    have := ZMod.natCast_self (k + 1)
    push_cast at this ⊢
    linear_combination 4 * this
  simpa [e] using this

theorem ne_one (hd : 0 < d) : χ ≠ 1 := fun h => by
  have := hχ.apply_neg_one hd
  rw [h, MulChar.one_apply isUnit_one.neg] at this
  norm_num at this

end IsKroneckerChar

theorem isKroneckerChar_of_jacobiSym {d : ℕ} (hd : d % 4 = 3) {χ : DirichletCharacter ℂ d}
    (h : ∀ n : ℕ, χ n = (J(n | d) : ℤ)) : IsKroneckerChar χ := fun n hn => by
  rw [h, jacobiSym.neg _ hn]
  congr 1
  rcases Nat.odd_mod_four_iff.1 (Nat.odd_iff.1 hn) with h1 | h1
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 (by omega))]
  · rw [ZMod.χ₄_nat_three_mod_four h1, jacobiSym.quadratic_reciprocity_three_mod_four h1 hd]
    ring

theorem isKroneckerChar_quadraticChar {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3) :
    IsKroneckerChar ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) :=
  isKroneckerChar_of_jacobiSym hd fun n => by
    simp [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]

theorem exists_isKroneckerChar {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 3) :
    ∃ χ : DirichletCharacter ℂ d, IsKroneckerChar χ := by
  haveI : NeZero d := ⟨hd0⟩
  rcases hd with hd | hd
  · obtain ⟨k, hk⟩ : 4 ∣ d := Nat.dvd_of_mod_eq_zero hd
    let f : ℕ → ℤ := fun n => if Odd n then J(-(d : ℤ) | n) else 0
    have hf : ∀ n, f (n % d) = f n := fun n => by
      have : Odd (n % d) ↔ Odd n := by
        rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd _ ⟨2 * k, by omega⟩]
      simp only [f, this]
      split_ifs with h
      · have e : -(d : ℤ) = 4 * -k := by rw [hk]; push_cast; ring
        rw [e, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four h,
          jacobiSym.at_four (this.2 h), jacobiSym.mod_right _ h, hk]
        simp
      · rfl
    refine ⟨⟨⟨⟨fun x => f x.val, ?_⟩, fun x y => ?_⟩, fun x hx => ?_⟩, fun n hn => ?_⟩
    · rw [← Nat.cast_one (R := ZMod d), ZMod.val_natCast, hf]
      simp [f]
    · simp only [ZMod.val_mul, hf, f, Nat.odd_mul]
      by_cases h1 : Odd x.val <;> by_cases h2 : Odd y.val <;> simp [h1, h2]
      rw [jacobiSym.mul_right' _ h1.pos.ne' h2.pos.ne', Int.cast_mul]
    · simp only [f]
      split_ifs with h
      · rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
        rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
        exact ⟨h.pos.ne', by rwa [Int.neg_gcd, Int.gcd_natCast_natCast, Nat.gcd_comm]⟩
      · simp
    · change ((f (n : ZMod d).val : ℤ) : ℂ) = _
      rw [ZMod.val_natCast, hf]
      simp [f, hn]
  · have hf : ∀ n : ℕ, J(((n % d : ℕ) : ℤ) | d) = J(n | d) := fun n => by
      rw [jacobiSym.mod_left n]; simp
    refine ⟨⟨⟨⟨fun x => (J(x.val | d) : ℤ), ?_⟩, fun x y => ?_⟩, fun x hx => ?_⟩,
      isKroneckerChar_of_jacobiSym hd fun n => ?_⟩
    · rw [← Nat.cast_one (R := ZMod d), ZMod.val_natCast, hf]
      simp
    · simp only [ZMod.val_mul, hf]
      rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]
    · rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
      change ((J(x.val | d) : ℤ) : ℂ) = 0
      rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
      exact ⟨hd0, by rwa [Int.gcd_natCast_natCast]⟩
    · change ((J((n : ZMod d).val | d) : ℤ) : ℂ) = _
      rw [ZMod.val_natCast, hf]

variable {K : Type*} [Field K] [NumberField K] {d : ℕ}

theorem exists_isKroneckerChar_of_discr (h2 : finrank ℚ K = 2) (hD : discr K = -d) :
    ∃ χ : DirichletCharacter ℂ d, IsKroneckerChar χ := by
  have := discr_mod_four h2
  have := discr_ne_zero K
  exact exists_isKroneckerChar (by omega) (by omega)

theorem dedekindZeta_eq_mul_LFunction [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  have hκ : ∀ p : ℕ, p.Prime → χ p = kroneckerAt (discr K) p := fun p hp => by
    rw [kroneckerAt, hD]
    split_ifs with h
    · have := discr_mod_four h2
      subst h
      exact hχ.apply_two (by omega)
    · exact hχ p (hp.odd_of_ne_two h)
  rw [χ.LFunction_eq_LSeries hs, ← LSeries_one_eq_riemannZeta hs, ← LSeries_convolution'
    (LSeriesSummable_one_iff.2 hs) (χ.LSeriesSummable_of_one_lt_re hs), dedekindZeta]
  refine LSeries_congr (fun {n} hn => ?_) s
  have := idealCount_eq_sum h2 (fun n => χ n) (by simp) (by simp) hκ hn
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, one_mul]
  rw [Nat.sum_divisorsAntidiagonal' (fun _ e => χ e), ← this]
  rfl

end GlobalTheory
