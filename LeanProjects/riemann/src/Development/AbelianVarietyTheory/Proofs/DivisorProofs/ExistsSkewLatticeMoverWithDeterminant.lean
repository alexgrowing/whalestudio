import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalAboveOfDvdNormHost
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

open GlobalTheory.NormSum

noncomputable section

namespace GlobalTheory.SkewCentral

theorem nat_split (m : ℕ) : ∀ N : ℕ, 0 < N → ∃ a b : ℕ, N = a * b ∧ a ∣ m ^ N ∧ Nat.Coprime b m := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hc : Nat.Coprime N m
    · exact ⟨1, N, by ring, one_dvd _, hc⟩
    · obtain ⟨p, hp, hpN, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
      obtain ⟨N1, rfl⟩ := hpN
      have hN1 : 0 < N1 := Nat.pos_of_mul_pos_left hN
      have hlt : N1 < p * N1 := by nlinarith [hp.two_le]
      obtain ⟨a, b, e, ha, hb⟩ := ih N1 hlt hN1
      refine ⟨p * a, b, by rw [e]; ring, ?_, hb⟩
      calc p * a ∣ m * m ^ N1 := Nat.mul_dvd_mul hpm ha
        _ = m ^ (N1 + 1) := by ring
        _ ∣ m ^ (p * N1) := pow_dvd_pow m (by nlinarith [hp.two_le])

theorem exists_sym_idem (D : D7) (m : ℕ) (hm : 0 < m) : ∃ e ∈ OhE D, e * e = e ∧ sgA D e = e ∧
    (∀ n : ℕ, 0 < n → Nat.Coprime n m → ∃ w ∈ OhE D, e = (n : AE D) * w) ∧
    (∀ k : ℕ, ∃ w ∈ OhE D, 1 - e = (m : AE D) ^ k * w) := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl m hm
  have h2 : ∀ k : ℕ, ∃ v ∈ OhE D, f = (m : AE D) ^ k * v := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, h⟩ := ih
      refine ⟨v * w, mul_mem hv hw, ?_⟩
      calc f = f * f := hff.symm
        _ = ((m : AE D) ^ k * v) * ((m : AE D) * w) := by rw [← h, ← hfw]
        _ = _ := by ring
  have hsf : sgA D f * sgA D f = sgA D f := by rw [← map_mul, hff]
  refine ⟨1 - f * sgA D f, sub_mem (one_mem _) (mul_mem hf (VacMove.sgA_mem D hf)), ?_, ?_, ?_, ?_⟩
  · linear_combination (sgA D f * sgA D f) * hff + f * hsf - 0 * hff
  · rw [map_sub, map_one, map_mul, VacMove.sgA_sgA, mul_comm]
  · intro n hn hnm
    obtain ⟨v, hv, e⟩ := h3 n hn hnm.symm
    have e' := congrArg (sgA D) e
    rw [map_sub, map_one, map_mul, map_natCast] at e'
    refine ⟨v + f * sgA D v, add_mem hv (mul_mem hf (VacMove.sgA_mem D hv)), ?_⟩
    linear_combination e + f * e'
  · intro k
    obtain ⟨v, hv, e⟩ := h2 k
    exact ⟨v * sgA D f, mul_mem hv (VacMove.sgA_mem D hf), by rw [e]; ring⟩

theorem exists_max_over (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Ideal.absNorm 𝔪) : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 D.host.E) ∈ P := by
  first
  | exact @_root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host
  | exact _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host
  | (apply _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> assumption)
  | (intros; apply _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MaximalIdealDividingNorm.exists_maximal_above_of_dvd_norm_host ..)

theorem coprime_of_inert (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) (hc : IsCoprime 𝔪 (D.host.conj • 𝔪))
    {q : ℕ} (hq : q.Prime) (hi : InertQ D q) : Nat.Coprime q (Ideal.absNorm 𝔪) := by
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  obtain ⟨P, hP, hle, hqP⟩ := exists_max_over D 𝔪 h0 hq hd
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hcP := hi P hP.isPrime hP0 hqP
  have h2 : D.host.conj • 𝔪 ≤ P := hcP ▸ Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hle
  rw [Ideal.isCoprime_iff_sup_eq] at hc
  exact hP.ne_top (eq_top_iff.2 (hc ▸ sup_le hle h2))

theorem dvd_of_mem (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Ideal.absNorm 𝔪) {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ 𝔪) : p ∣ m := by
  by_contra h
  obtain ⟨P, hP, hle, hpP⟩ := exists_max_over D 𝔪 h0 hp hd
  have hcop : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  obtain ⟨u, v, e⟩ := hcop
  have e' := congrArg (Int.cast : ℤ → 𝓞 D.host.E) e
  push_cast at e'
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpP) (Ideal.mul_mem_left _ _ (hle hm))

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

def glue (D : D7) (e : AE D) (a : D.host.E) : AE D := e * inc D a + (1 - e)

theorem glue_mul (D : D7) {e : AE D} (he : e * e = e) (a b : D.host.E) :
    glue D e a * glue D e b = glue D e (a * b) := by
  unfold glue; rw [map_mul]
  linear_combination (inc D a * inc D b - inc D a - inc D b + 1) * he

theorem glue_one (D : D7) (e : AE D) : glue D e 1 = 1 := by
  unfold glue; rw [map_one]; ring

theorem sgA_glue (D : D7) {e : AE D} (hs : sgA D e = e) (a : D.host.E) :
    sgA D (glue D e a) = glue D e (D.host.conj a) := by
  unfold glue; rw [map_add, map_mul, map_sub, map_one, hs, PtsMem.sgA_inc]

def glueU (D : D7) {e : AE D} (he : e * e = e) (a : D.host.E) (ha : a ≠ 0) : (AE D)ˣ :=
  ⟨glue D e a, glue D e a⁻¹, by rw [glue_mul D he, mul_inv_cancel₀ ha, glue_one],
    by rw [glue_mul D he, inv_mul_cancel₀ ha, glue_one]⟩

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← AlgEquiv.mul_apply, VacInt.conj_mul_self]; rfl

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

theorem natCast_mem_conj (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {M : ℕ} (h : (M : 𝓞 D.host.E) ∈ 𝔪) :
    (M : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : D.host.conj⁻¹ • (M : 𝓞 D.host.E) = M :=
    map_natCast (MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj⁻¹) M
  rwa [this]

theorem exists_skew_scalar (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h0 : 𝔪 ≠ ⊥) (hc : IsCoprime 𝔪 (D.host.conj • 𝔪)) :
    ∃ y s : (AE D)ˣ, s * sgU D s = 1 ∧ y = s * sgU D y ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((y : AE D) - 1) ∧ ZeroAt D q ((s : AE D) - 1)) ∧
      ∀ t : D.host.E, t ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
        ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :
          FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ↔
        ((s⁻¹ : (AE D)ˣ) : AE D) * inc D t ∈ OhE D := by
  set ι := algebraMap (𝓞 D.host.E) D.host.E with hι
  set M := Ideal.absNorm 𝔪 with hMdef
  have hM : 0 < M := Nat.pos_of_ne_zero (by rwa [hMdef, Ne, Ideal.absNorm_eq_zero_iff])
  have hMm : (M : 𝓞 D.host.E) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  have hMc := natCast_mem_conj D 𝔪 hMm
  obtain ⟨m0, n0, β, hm0, hn0, hmn, hm0B, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator 𝔪 h0
  have hn0M : Nat.Coprime n0 M := by
    apply Nat.coprime_of_dvd
    intro p hp hpn hpM
    have h1 := dvd_of_mem D 𝔪 h0 hp hpM hm0B
    exact hp.not_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd h1 hpn)
  obtain ⟨e, heO, hee, hse, hen, hem⟩ := exists_sym_idem D M hM
  have hβE : ι β ≠ 0 := by
    rw [hι, Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]; exact hβ0
  set b' := D.host.conj (ι β) with hb'
  have hb'0 : b' ≠ 0 := by rw [hb', Ne, map_eq_zero_iff _ D.host.conj.injective]; exact hβE
  have hzero : ∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q e := by
    intro q hq hi k
    have hcop := coprime_of_inert D 𝔪 h0 hc hq hi
    obtain ⟨w, hw, he'⟩ := hen (q ^ k) (pow_pos hq.pos k) (Nat.Coprime.pow_left k hcop)
    exact ⟨1, one_pos, Nat.coprime_one_left _, w, hw, by rw [he']; push_cast; ring⟩
  refine ⟨glueU D hee (ι β) hβE, glueU D hee (ι β / b') (div_ne_zero hβE hb'0), ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    change glue D e _ * sgA D (glue D e _) = 1
    have : ι β / b' * D.host.conj (ι β / b') = 1 := by
      rw [map_div₀, ← hb', conj_conj]; field_simp
    rw [sgA_glue D hse, glue_mul D hee, this, glue_one]
  · apply Units.ext
    change glue D e _ = glue D e _ * sgA D (glue D e _)
    rw [sgA_glue D hse, glue_mul D hee, ← hb', div_mul_cancel₀ _ hb'0]
  · intro q hq hi
    constructor
    · have := VacMove.zeroAt_mul D hq (hzero q hq hi) (inc D (ι β) - 1)
      convert this using 1
      change glue D e _ - 1 = _
      unfold glue; ring
    · have := VacMove.zeroAt_mul D hq (hzero q hq hi) (inc D (ι β / b') - 1)
      convert this using 1
      change glue D e _ - 1 = _
      unfold glue; ring
  · intro t
    change _ ↔ glue D e (ι β / b')⁻¹ * inc D t ∈ OhE D
    rw [inv_div]
    have hc0 : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
      intro hb
      rw [hb, Ideal.mem_bot] at hMc
      exact hM.ne' (by exact_mod_cast hMc)
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hc0]
    simp only [FractionalIdeal.mem_coeIdeal]

    constructor
    · intro ht
      obtain ⟨a1, ha1, e1⟩ := ht _ ⟨D.host.conj • β, Ideal.smul_mem_pointwise_smul _ _ _ hβB, rfl⟩
      obtain ⟨a2, ha2, e2⟩ := ht _ ⟨(M : 𝓞 D.host.E), hMc, rfl⟩
      rw [Formalism.L2.Pj.algebraMap_conj_smul, ← hι, ← hb'] at e1
      rw [map_natCast] at e2
      obtain ⟨c, hc⟩ := hdvd a1 ha1
      have hc' : ι c = (n0 : D.host.E) * (b' / ι β) * t := by
        have := congrArg ι hc
        rw [map_mul, map_mul, map_natCast, e1] at this
        field_simp
        linear_combination -this
      obtain ⟨w, hw, ew⟩ := hen n0 hn0 hn0M
      obtain ⟨w', hw', ew'⟩ := hem 1
      have key : glue D e (b' / ι β) * inc D t = w * inc D (ι c) + w' * inc D (ι a2) := by
        rw [hc', e2, map_mul, map_mul, map_mul, map_natCast, map_natCast]
        unfold glue
        linear_combination (inc D (b' / ι β) * inc D t) * ew + inc D t * ew'
      rw [key]
      exact add_mem (mul_mem hw ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe c)))
        (mul_mem hw' ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (RingOfIntegers.isIntegral_coe a2)))
    · intro hX y ⟨b0, hb0, hy⟩
      subst hy
      have hX1 : e * inc D (b' / ι β * t) ∈ OhE D := by
        have := mul_mem heO hX
        convert this using 1
        unfold glue
        rw [map_mul]
        linear_combination (inc D t - inc D (b' / ι β) * inc D t) * hee
      have hX2 : (1 - e) * inc D t ∈ OhE D := by
        have := mul_mem (sub_mem (one_mem _) heO) hX
        convert this using 1
        unfold glue
        linear_combination (inc D (b' / ι β) * inc D t - inc D t) * hee

      obtain ⟨N, hN, hNu⟩ := VacMove.exists_nat_denom D (inc D (b' / ι β * t))
      obtain ⟨a, b, hab, ha, hb⟩ := nat_split M N hN
      obtain ⟨wN, hwN, ewN⟩ := hem N
      obtain ⟨a', ha'⟩ := ha
      have ewN' : 1 - e = (a : AE D) * (a' : AE D) * wN := by
        rw [ewN]; exact_mod_cast (congrArg (fun n : ℕ => (n : AE D) * wN) ha')
      have hNab : (N : AE D) = (a : AE D) * (b : AE D) := by exact_mod_cast congrArg (Nat.cast : ℕ → AE D) hab
      have hbU : inc D ((b : D.host.E) * (b' / ι β * t)) ∈ OhE D := by
        have e3 : inc D ((b : D.host.E) * (b' / ι β * t)) =
            (b : AE D) * (e * inc D (b' / ι β * t)) + (wN * a') * ((N : AE D) * inc D (b' / ι β * t)) := by
          rw [map_mul (inc D), map_natCast]
          linear_combination ((b : AE D) * inc D (b' / ι β * t)) * ewN' -
            (wN * a' * inc D (b' / ι β * t)) * hNab
        rw [e3]
        exact add_mem (mul_mem (natCast_mem _ _) hX1) (mul_mem (mul_mem hwN (natCast_mem _ _)) hNu)
      obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1
        ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hbU)

      obtain ⟨N', hN', hNt⟩ := VacMove.exists_nat_denom D (inc D t)
      obtain ⟨a2, b2, hab2, ha2, hb2⟩ := nat_split M N' hN'
      have hb2pos : 0 < b2 := Nat.pos_of_ne_zero (by rintro rfl; simp at hab2; omega)
      obtain ⟨w2, hw2, ew2⟩ := hen b2 hb2pos hb2
      have hNab2 : (N' : AE D) = (a2 : AE D) * (b2 : AE D) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → AE D) hab2
      have hat : inc D ((a2 : D.host.E) * t) ∈ OhE D := by
        have e3 : inc D ((a2 : D.host.E) * t) = (a2 : AE D) * ((1 - e) * inc D t) + w2 * ((N' : AE D) * inc D t) := by
          rw [map_mul (inc D), map_natCast]
          linear_combination ((a2 : AE D) * inc D t) * ew2 - (w2 * inc D t) * hNab2
        rw [e3]
        exact add_mem (mul_mem (natCast_mem _ _) hX2) (mul_mem hw2 hNt)
      obtain ⟨r2, hr2⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).1
        ((GlobalTheory.HeckeVal.inc_mem_iff D _).1 hat)
      obtain ⟨a2', ha2'⟩ := ha2
      have hbpos : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; omega)

      have hinv : D.host.conj⁻¹ = D.host.conj := inv_eq_of_mul_eq_one_right (VacInt.conj_mul_self D)
      have hc0 : D.host.conj • b0 ∈ 𝔪 := by
        have := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hb0
        rwa [hinv] at this
      obtain ⟨c, hc⟩ := hdvd _ hc0
      have hE : (n0 : D.host.E) * ι b0 = b' * D.host.conj (ι c) := by
        have := congrArg (fun x => D.host.conj (ι x)) hc
        simp only [hι, map_mul, map_natCast, Formalism.L2.Pj.algebraMap_conj_smul, conj_conj] at this
        rw [hb']; exact this
      have hcop : IsCoprime ((b * n0 : ℕ) : ℤ) ((M ^ (N' + 1) : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.Coprime.mul hb hn0M))
      obtain ⟨u', v', huv⟩ := hcop
      have huv' := congrArg (Int.cast : ℤ → D.host.E) huv
      push_cast at huv'
      have hM' : (M : D.host.E) ^ N' = (a2 : D.host.E) * a2' := by exact_mod_cast ha2'
      have hr' : ι r * ι β = b * b' * t := by rw [hr]; field_simp
      refine ⟨(u' : 𝓞 D.host.E) * ((r * (D.host.conj • c)) * β) + (v' : 𝓞 D.host.E) * (((a2' : 𝓞 D.host.E) * r2 * b0) * M),
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβB))
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hMm)), ?_⟩
      have fin : (u' : D.host.E) * (ι r * D.host.conj (ι c) * ι β) + (v' : D.host.E) * ((a2' : D.host.E) * ι r2 * ι b0 * M) =
          t * ι b0 := by
        rw [hr2]
        linear_combination (u' * D.host.conj (ι c)) * hr' - (u' * b * t) * hE -
          (v' * t * ι b0 * M) * hM' + (t * ι b0) * huv'
      simp only [map_add, map_mul, map_intCast, map_natCast, Formalism.L2.Pj.algebraMap_conj_smul]
      exact fin

end GlobalTheory.SkewCentral

namespace GlobalTheory.SkewCentral

theorem exists_central_skew_move : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ,
    ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧
      x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' ∧ ∀ h : GA D d, h * g' = g' * h := by
  intro D 𝔪 h0 hc d
  obtain ⟨y, s, hss, hys, hin, hmv⟩ := exists_skew_scalar D 𝔪 h0 hc
  let g : GL (Fin d) (AE D) :=
    Units.map (Matrix.scalar (Fin d) : AE D →+* Matrix (Fin d) (Fin d) (AE D)).toMonoidHom s
  have hgv : (g : Matrix (Fin d) (Fin d) (AE D)) = Matrix.scalar (Fin d) (s : AE D) := rfl
  have hgi : ((g⁻¹ : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) =
      Matrix.scalar (Fin d) ((s⁻¹ : (AE D)ˣ) : AE D) := rfl
  have hsg : sgA D (s : AE D) * s = 1 := by
    have := congrArg Units.val hss
    rw [Units.val_mul, Units.val_one, mul_comm] at this
    exact this
  have hgA : g ∈ GA D d := by
    rw [PtsMem.mem_GA, hgv]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hsg]
    · simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hij]
  refine ⟨⟨g, hgA⟩, y ^ d, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hi i j
    change ZeroAt D q ((Matrix.scalar (Fin d) (s : AE D)) i j - (1 : Matrix (Fin d) (Fin d) (AE D)) i j)
    by_cases hij : i = j
    · subst hij
      simpa [Matrix.scalar_apply] using (hin q hq hi).2
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, sub_zero]
      intro k
      exact ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩
  · intro x
    change _ ↔ ∀ i, (Matrix.scalar (Fin d) ((s⁻¹ : (AE D)ˣ) : AE D)).mulVec (fun j => inc D (x j)) i ∈ OhE D
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_implies, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    exact forall_congr' fun i => hmv (x i)
  · intro q hq hi
    obtain ⟨c, hc'⟩ := sub_dvd_pow_sub_pow (y : AE D) 1 d
    have e : (y : AE D) ^ d - 1 = ((y : AE D) - 1) * c := by rw [← hc', one_pow]
    rw [Units.val_pow_eq_pow_val, e]
    exact VacMove.zeroAt_mul D hq (hin q hq hi).1 c
  · have hdet : Matrix.GeneralLinearGroup.det g = s ^ d := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, Units.val_pow_eq_pow_val, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change y ^ d = Matrix.GeneralLinearGroup.det g * sgU D (y ^ d)
    rw [hdet, map_pow, ← mul_pow, ← hys]
  · intro h
    apply Subtype.ext
    apply Units.ext
    change (((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))) * Matrix.scalar (Fin d) (s : AE D) =
      Matrix.scalar (Fin d) (s : AE D) * ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D))
    exact (Matrix.scalar_commute (s : AE D) (fun _ => Commute.all _ _) _).eq.symm

end GlobalTheory.SkewCentral
