import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

section Core

variable {F : Type} [NormedField F] [IsUltrametricDist F]

theorem norm_int_le (m : ℤ) : ‖(m : F)‖ ≤ 1 := by
  apply Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_le_one_of_int
  have h := isIntegral_algebraMap (R := ℤ) (A := F) (x := m)
  simpa using h

theorem norm_add_eq_sub {x y : F} (h : ‖x‖ ≠ ‖y‖) : ‖x + y‖ = ‖x - y‖ := by
  have h' : ‖x‖ ≠ ‖-y‖ := by rwa [norm_neg]
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h', norm_neg]

theorem not_both {p : ℕ} (hp : p.Prime) {s t : ℤ} (hst : IsCoprime s t) (hs : (p : ℤ) ∣ s) (ht : (p : ℤ) ∣ t) : False := by
  have h := hst.isUnit_of_dvd' hs ht
  rw [Int.ofNat_isUnit, Nat.isUnit_iff] at h
  exact hp.one_lt.ne' h

theorem not_dvd_form (p d : ℕ) [Fact p.Prime] (hpd : ¬ p ∣ d) (hJ : jacobiSym (-(d : ℤ)) p ≠ 1) {s t : ℤ} (hst : IsCoprime s t) :
    ¬ (p : ℤ) ∣ s ^ 2 + d * t ^ 2 := by
  intro hdiv
  have hz : ((s : ZMod p)) ^ 2 + (d : ZMod p) * (t : ZMod p) ^ 2 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (s ^ 2 + d * t ^ 2) p).2 hdiv
    push_cast at h
    exact h
  have hd0 : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (-(d : ℤ)) p).1 h0
    rw [dvd_neg] at h1
    exact hpd (by exact_mod_cast h1)
  by_cases ht : (t : ZMod p) = 0
  · rw [ht] at hz
    have hs0 : (s : ZMod p) = 0 := by simpa using hz
    exact not_both (Fact.out : p.Prime) hst ((ZMod.intCast_zmod_eq_zero_iff_dvd s p).1 hs0)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd t p).1 ht)
  · apply hJ
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hd0]
    refine ⟨(s : ZMod p) / (t : ZMod p), ?_⟩
    push_cast
    field_simp
    linear_combination -hz

theorem core_coprime (p d : ℕ) [Fact p.Prime] (hd : d.Prime) (hJ : jacobiSym (-(d : ℤ)) p ≠ 1)
    (h1 : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → ‖(m : F)‖ = 1) (hlt : ‖(p : F)‖ < 1) (hp0 : (p : F) ≠ 0) (r : F) (hr : r ^ 2 = -(d : F))
    (s t : ℤ) (hst : IsCoprime s t) : ‖(s : F) + t * r‖ = ‖(s : F) - t * r‖ := by
  have hr1 : ‖r‖ ^ 2 = ‖(d : F)‖ := by rw [← norm_pow, hr, norm_neg]
  by_cases hpd : p ∣ d
  · have hpd' : p = d := (Nat.prime_dvd_prime_iff_eq Fact.out hd).1 hpd
    have hr2 : ‖r‖ ^ 2 = ‖(p : F)‖ := by rw [hr1, hpd']
    have hpp : 0 < ‖(p : F)‖ := norm_pos_iff.2 hp0
    have hrn : 0 ≤ ‖r‖ := norm_nonneg r
    have hrpos : 0 < ‖r‖ := by
      rcases hrn.lt_or_eq with h | h
      · exact h
      · rw [← h] at hr2; norm_num at hr2; linarith
    have hrlt : ‖r‖ < 1 := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith
    have hplt : ‖(p : F)‖ < ‖r‖ := by rw [← hr2]; nlinarith
    apply norm_add_eq_sub
    by_cases hs : (p : ℤ) ∣ s
    · have ht : ¬ (p : ℤ) ∣ t := fun ht => not_both (Fact.out : p.Prime) hst hs ht
      obtain ⟨s', rfl⟩ := hs
      have e1 : ‖(((p : ℤ) * s' : ℤ) : F)‖ ≤ ‖(p : F)‖ := by
        push_cast
        rw [norm_mul]
        exact mul_le_of_le_one_right hpp.le (norm_int_le s')
      rw [norm_mul, h1 t ht, one_mul]
      exact (lt_of_le_of_lt e1 hplt).ne
    · rw [h1 s hs, norm_mul]
      have : ‖(t : F)‖ * ‖r‖ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hrn (norm_int_le t)) hrlt
      exact this.ne'
  · have hn := h1 _ (not_dvd_form p d hpd hJ hst)
    have hrle : ‖r‖ ≤ 1 := by
      have hdle : ‖(d : F)‖ ≤ 1 := by simpa using norm_int_le (F := F) (d : ℤ)
      by_contra hc
      rw [not_le] at hc
      nlinarith [norm_nonneg r]
    have htr : ‖(t : F) * r‖ ≤ 1 := by
      rw [norm_mul]; exact mul_le_one₀ (norm_int_le t) (norm_nonneg r) hrle
    have hA : ‖(s : F) + t * r‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le s) htr)
    have hA' : ‖(s : F) - t * r‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le s) (by rwa [norm_neg]))
    have hprod : ‖(s : F) + t * r‖ * ‖(s : F) - t * r‖ = 1 := by
      rw [← norm_mul, ← hn]
      congr 1
      push_cast
      linear_combination (-(t : F) ^ 2) * hr
    have hA1 : ‖(s : F) + t * r‖ = 1 := by
      apply le_antisymm hA
      by_contra hc
      rw [not_le] at hc
      nlinarith [norm_nonneg ((s : F) + t * r), norm_nonneg ((s : F) - t * r)]
    rw [hA1, one_mul] at hprod
    rw [hA1, hprod]

theorem core_int (p d : ℕ) [Fact p.Prime] (hd : d.Prime) (hJ : jacobiSym (-(d : ℤ)) p ≠ 1)
    (h1 : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → ‖(m : F)‖ = 1) (hlt : ‖(p : F)‖ < 1) (hp0 : (p : F) ≠ 0) (r : F) (hr : r ^ 2 = -(d : F))
    (s t : ℤ) : ‖(s : F) + t * r‖ = ‖(s : F) - t * r‖ := by
  by_cases h0 : Int.gcd s t = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.1 h0
    simp
  · obtain ⟨s', t', hg, hs, ht⟩ := Int.exists_gcd_one (Nat.pos_of_ne_zero h0)
    have hc := core_coprime p d hd hJ h1 hlt hp0 r hr s' t' (Int.isCoprime_iff_gcd_eq_one.2 hg)
    have hsF : (s : F) = (s' : F) * ((Int.gcd s t : ℕ) : F) := by exact_mod_cast congrArg (Int.cast : ℤ → F) hs
    have htF : (t : F) = (t' : F) * ((Int.gcd s t : ℕ) : F) := by exact_mod_cast congrArg (Int.cast : ℤ → F) ht
    have e1 : (s : F) + t * r = ((Int.gcd s t : ℕ) : F) * ((s' : F) + t' * r) := by rw [hsF, htF]; ring
    have e2 : (s : F) - t * r = ((Int.gcd s t : ℕ) : F) * ((s' : F) - t' * r) := by rw [hsF, htF]; ring
    rw [e1, e2, norm_mul, norm_mul, hc]

theorem core_rat [CharZero F] (p d : ℕ) [Fact p.Prime] (hd : d.Prime) (hJ : jacobiSym (-(d : ℤ)) p ≠ 1)
    (h1 : ∀ m : ℤ, ¬ (p : ℤ) ∣ m → ‖(m : F)‖ = 1) (hlt : ‖(p : F)‖ < 1) (r : F) (hr : r ^ 2 = -(d : F))
    (a b : ℚ) : ‖(a : F) + b * r‖ = ‖(a : F) - b * r‖ := by
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha : (a.den : F) ≠ 0 := Nat.cast_ne_zero.2 a.den_ne_zero
  have hb : (b.den : F) ≠ 0 := Nat.cast_ne_zero.2 b.den_ne_zero
  have e : ∀ σ : F, (a : F) + b * σ =
      (((a.num * b.den : ℤ) : F) + ((b.num * a.den : ℤ) : F) * σ) / ((a.den : F) * (b.den : F)) := by
    intro σ
    rw [Rat.cast_def a, Rat.cast_def b]
    push_cast
    field_simp
  have e2 : (a : F) - b * r =
      (((a.num * b.den : ℤ) : F) - ((b.num * a.den : ℤ) : F) * r) / ((a.den : F) * (b.den : F)) := by
    have := e (-r)
    rw [mul_neg, ← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
    exact this
  rw [e r, e2, norm_div, norm_div, core_int p d hd hJ h1 hlt hp0 r hr]

end Core

section Host

open Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Host R)

theorem K_repr (k : H.K) : ∃ a b : ℚ, (k : H.E) = (a : H.E) + (b : H.E) * H.sqd := by
  have hβ := bE_sq H
  refine K_induction H (p := fun x => ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqd) ?_ ?_ ?_ ?_ ?_ k
  · exact ⟨0, 1, by simp⟩
  · intro r
    exact ⟨r, 0, by simp⟩
  · rintro x y ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by push_cast; ring⟩
  · rintro x ⟨a, b, rfl⟩
    by_cases h0 : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨0, 0, by simp⟩
    · have hd : (0 : ℚ) < H.d := by exact_mod_cast d_pos H
      have hN : a ^ 2 + (H.d : ℚ) * b ^ 2 ≠ 0 := by
        intro hz
        apply h0
        have h1 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, mul_nonneg hd.le (sq_nonneg b)]
        have h2 : (H.d : ℚ) * b ^ 2 = 0 := by nlinarith [sq_nonneg a, mul_nonneg hd.le (sq_nonneg b)]
        refine ⟨by simpa using h1, ?_⟩
        have h3 := (mul_eq_zero.1 h2).resolve_left hd.ne'
        simpa using h3
      have hNE : (a : H.E) ^ 2 + (H.d : H.E) * (b : H.E) ^ 2 ≠ 0 := by exact_mod_cast hN
      refine ⟨a / (a ^ 2 + (H.d : ℚ) * b ^ 2), -b / (a ^ 2 + (H.d : ℚ) * b ^ 2), ?_⟩
      apply inv_eq_of_mul_eq_one_right
      push_cast
      have e : ((a : H.E) + (b : H.E) * H.sqd) *
          ((a : H.E) / ((a : H.E) ^ 2 + (H.d : H.E) * (b : H.E) ^ 2) +
            -(b : H.E) / ((a : H.E) ^ 2 + (H.d : H.E) * (b : H.E) ^ 2) * H.sqd) =
          ((a : H.E) ^ 2 - (b : H.E) ^ 2 * H.sqd ^ 2) / ((a : H.E) ^ 2 + (H.d : H.E) * (b : H.E) ^ 2) := by ring
      rw [e, hβ, div_eq_one_iff_eq hNE]
      ring
  · rintro x y ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a * a' - H.d * b * b', a * b' + a' * b, by push_cast; linear_combination ((b : H.E) * b') * hβ⟩

end Host

section Main

variable {D : D7}

theorem norm_int_unit (p : ℕ) [Fact p.Prime] (m : ℤ) (h : ¬ (p : ℤ) ∣ m) : ‖(m : ℂ_[p])‖ = 1 := by
  have hc : Nat.Coprime m.natAbs p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hd
    exact h (Int.natCast_dvd.2 hd)
  have h1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.norm_nat_coprime p hc
  have h2 : ‖(m : ℂ_[p])‖ = ‖((m.natAbs : ℕ) : ℂ_[p])‖ := by
    rcases Int.natAbs_eq m with e | e
    · conv_lhs => rw [e]
      simp
    · conv_lhs => rw [e]
      simp
  rw [h2, h1]

theorem norm_p_lt (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := by
    first
      | exact padicNormE.norm_p_lt_one
      | exact Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem nonsplit_conj (p : ℕ) [Fact p.Prime] (hs : ¬ SplitK D p) (ι : ℂ ≃+* ℂ_[p]) (x : D.host.K) :
    ‖ι (D.host.φ₀ (D.host.conj (x : D.host.E)))‖ = ‖ι (D.host.φ₀ (x : D.host.E))‖ := by
  have hJ : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := fun h => hs (Or.inr h)
  obtain ⟨a, b, hx⟩ := K_repr D.host x
  have hr : (ι (Complex.I * (Real.sqrt D.host.d : ℂ))) ^ 2 = -(D.host.d : ℂ_[p]) := by
    rw [← map_pow]
    have h : (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 = -(D.host.d : ℂ) := by
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rw [h, map_neg, map_natCast]
  have e1 : ι (D.host.φ₀ (x : D.host.E)) = (a : ℂ_[p]) + b * ι (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [hx, map_add, map_mul, phi_b, map_ratCast, map_ratCast, map_add, map_mul, map_ratCast, map_ratCast]
  have e2 : ι (D.host.φ₀ (D.host.conj (x : D.host.E))) = (a : ℂ_[p]) - b * ι (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [hx, map_add, map_mul, conj_b, map_ratCast, map_ratCast, mul_neg, ← sub_eq_add_neg, map_sub, map_mul, phi_b,
      map_ratCast, map_ratCast, map_sub, map_mul, map_ratCast, map_ratCast]
  rw [e1, e2]
  exact (core_rat p D.host.d D.host.hyp.2.1 hJ (norm_int_unit p) (norm_p_lt p) _ hr a b).symm

theorem det_unit_nonsplit (p : ℕ) [Fact p.Prime] (hs : ¬ SplitK D p) (ι : ℂ ≃+* ℂ_[p]) (x : D.host.K)
    (h : D.host.φ₀ (x : D.host.E) * (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E)) = 1) : ‖ι (D.host.φ₀ (x : D.host.E))‖ = 1 := by
  have h1 := nonsplit_conj p hs ι x
  rw [phi_conj] at h1
  have h2 : ‖ι (D.host.φ₀ (x : D.host.E))‖ * ‖ι ((starRingEnd ℂ) (D.host.φ₀ (x : D.host.E)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, h, map_one, norm_one]
  rw [h1] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [sq]; exact h2)

end Main

section DetK

open Formalism.L2.Th1.H (stdLat imgLat relIdx IsIsom)

theorem stdH_apply' {m : Type} [Fintype m] [DecidableEq m] (L : PeriodPair) (x y : m → ℂ) :
    Formalism.L2.Th1.H.stdH L m x y = ∑ i, x i * ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * conj (y i) := by
  simp [Formalism.L2.Th1.H.stdH, Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply]

theorem mem_stdLat' {m : Type} {L : PeriodPair} {x : m → ℂ} : x ∈ stdLat L m ↔ ∀ i, x i ∈ L.lattice := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem area_ne (L : PeriodPair) : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
  have h : 0 < Formalism.L2.Th1.F.area L := by
    exact Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos L
  exact_mod_cast h.ne'

theorem unitary_det_gen (L : PeriodPair) {m : Type} [Fintype m] [DecidableEq m] (u : (m → ℂ) ≃ₗ[ℂ] (m → ℂ))
    (hiso : IsIsom (Formalism.L2.Th1.H.stdH L m) (Formalism.L2.Th1.H.stdH L m) (u : (m → ℂ) →ₗ[ℂ] (m → ℂ))) :
    LinearMap.det (u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (u : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1 := by
  set U := LinearMap.toMatrix' (u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hU
  set A : ℂ := ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) with hAdef
  have hA : A ≠ 0 := area_ne L
  have hUU : Matrix.conjTranspose U * U = 1 := by
    ext k j
    have h := hiso (Pi.single j 1) (Pi.single k 1)
    rw [stdH_apply', stdH_apply'] at h
    have hr : ∑ i, (Pi.single j 1 : m → ℂ) i * A⁻¹ * conj ((Pi.single k 1 : m → ℂ) i)
        = if k = j then A⁻¹ else 0 := by
      rw [Finset.sum_eq_single j]
      · by_cases hkj : k = j
        · subst hkj; simp
        · simp [hkj, Ne.symm hkj]
      · intro t _ ht; simp [Pi.single_apply, ht]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [← hAdef, hr] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hU, LinearMap.toMatrix'_apply]
    have e : ∑ i, star ((u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (Pi.single k 1) i) *
        (u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (Pi.single j 1) i
        = A * ∑ i, (u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (Pi.single j 1) i * A⁻¹ *
          conj ((u : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (Pi.single k 1) i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def]
      field_simp
    rw [e, h]
    split_ifs
    · field_simp
    · simp
  have hd' := congrArg Matrix.det hUU
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, hU, LinearMap.det_toMatrix'] at hd'
  rw [mul_comm]
  exact hd'

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem entries_in_K (hδ0 : δ ≠ 0) (hcc : cc ≠ ⊥) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (h1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) ≠ 0)
    (i j : Fin 4 × D.what₂.Tau) :
    ∃ x : D.host.K, u (Pi.single j 1) i = D.host.φ₀ (x : D.host.E) := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
  set ω : ℂ := δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) with hω
  have hωL : ω ∈ B.L.lattice := (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B ω).2 (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)
  set Lt := stdLat B.L (Fin 4 × D.what₂.Tau) with hLt
  set M := imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA with hM
  have hk2 : relIdx B.latA Lt ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.idx₂ B
  have hv : (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ) ∈ Lt := by
    rw [hLt, mem_stdLat']
    intro t
    by_cases h : t = j
    · subst h; simpa using hωL
    · rw [Pi.single_eq_of_ne h]; exact B.L.lattice.zero_mem
  have h2 : relIdx B.latA Lt • (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ) ∈ B.latA :=
    PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem B.latA Lt hv
  have h3 : u (relIdx B.latA Lt • (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ)) ∈ M := ⟨_, h2, rfl⟩
  have h4 : relIdx Lt M • u (relIdx B.latA Lt • (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ)) ∈ Lt :=
    PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem Lt M h3
  have hveq : (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ) = ω • (Pi.single j 1 : Fin 4 × D.what₂.Tau → ℂ) := by
    ext t
    by_cases h : t = j
    · subst h; simp
    · simp [h]
  have hz : (relIdx Lt M • u (relIdx B.latA Lt • (Pi.single j ω : Fin 4 × D.what₂.Tau → ℂ))) i
      = ((relIdx Lt M : ℂ) * (relIdx B.latA Lt : ℂ) * ω) * u (Pi.single j 1) i := by
    rw [hveq, map_nsmul, map_smul]
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, smul_eq_mul]
    ring
  obtain ⟨c', -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 ((mem_stdLat'.1 h4) i))
  rw [hz] at hc'
  have hcK : ((c : D.host.K)) ≠ 0 := by
    intro h
    exact hc0 (by exact_mod_cast h)
  have hφc : D.host.φ₀ (((c : D.host.K) : D.host.E)) ≠ 0 := by
    rw [Ne, map_eq_zero]
    intro h
    exact hcK (by exact_mod_cast h)
  have hk1C : (relIdx Lt M : ℂ) ≠ 0 := by exact_mod_cast h1
  have hk2C : (relIdx B.latA Lt : ℂ) ≠ 0 := by exact_mod_cast hk2
  refine ⟨(c' : D.host.K) / ((relIdx Lt M : D.host.K) * (relIdx B.latA Lt : D.host.K) * (c : D.host.K)), ?_⟩
  push_cast
  rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, eq_div_iff (mul_ne_zero (mul_ne_zero hk1C hk2C) hφc)]
  apply mul_left_cancel₀ hδ0
  rw [← hc', hω]
  ring

theorem det_in_K (hδ0 : δ ≠ 0) (hcc : cc ≠ ⊥) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (h1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) ≠ 0) :
    ∃ x : D.host.K, LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ (x : D.host.E) := by
  choose M hM using fun i j => entries_in_K B hδ0 hcc u h1 i j
  refine ⟨(Matrix.of M).det, ?_⟩
  have e : LinearMap.toMatrix' (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) =
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).mapMatrix (Matrix.of M) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    exact hM i j
  rw [← LinearMap.det_toMatrix', e, ← RingHom.map_det]
  rfl

theorem det_norm_nonsplit (hδ0 : δ ≠ 0) (hcc : cc ≠ ⊥) (p : ℕ) [Fact p.Prime] (hs : ¬ SplitK D p) (ι : ℂ ≃+* ℂ_[p])
    (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hiso : IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))
      (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (h1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) ≠ 0) :
    ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  obtain ⟨x, hx⟩ := det_in_K B hδ0 hcc u h1
  have h := unitary_det_gen B.L u hiso
  rw [hx] at h ⊢
  exact det_unit_nonsplit p hs ι x h

theorem kappaAt_nonsplit_of (hδ0 : δ ≠ 0) (hcc : cc ≠ ⊥) (p : ℕ) [Fact p.Prime] (hs : ¬ SplitK D p) (ι : ℂ ≃+* ℂ_[p])
    (hκ : ‖ι B.kappa‖ = 1) : B.KappaAt p ι := by
  intro u hiso h1 _ _
  rw [hκ, det_norm_nonsplit B hδ0 hcc p hs ι u hiso h1]
  norm_num

end DetK

end Formalism.L2.Ker.KS
