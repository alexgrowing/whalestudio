import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.ABInjective

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseC

variable {l : ℕ} [Fact l.Prime]

theorem ainf_φ : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  map_mem fun a => by rw [φ_aB]; exact aB_mem _

theorem ainf_σ (g : GQ l) : ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  map_mem fun a => by
    obtain ⟨a', h⟩ := σ_aB g a
    rw [h]; exact aB_mem _

theorem ι_u : ι l (u l) = qQ l ((l : ℚ_[l])⁻¹) := by
  refine inv_uniq (c := (l : BdR l)) ?_ ?_
  · rw [← map_natCast (ι l) l, ← map_mul, u_mul, map_one]
  · rw [← map_natCast (qQ l) l, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem ainf_plus : ∀ x ∈ Ainf' l, ι l x ∈ Plus l := fun x hx =>
  (Subring.closure_le (t := (Plus l).comap (ι l))).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · refine ⟨ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) a), ?_⟩
      exact (Loc2.lift_mk₀ (iC l) (isUnit_iC_l l) (isUnit_image_period l) _).symm
    · rw [Set.mem_singleton_iff.1 hy]
      show ι l (u l) ∈ Plus l
      rw [ι_u]
      exact ⟨algebraMap ℚ_[l] (BdRp l) _, rfl⟩) hx

theorem φpow_aB (h : ℕ) (a : AInf ℂ_[l] l) :
    (φ l ^ h) (aB l a) = aB l ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] a) := by
  induction h with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, φ_aB,
      Function.iterate_succ_apply']

theorem cancel_l {N : ℕ} {y z : B l} (h : (l : B l) ^ N * y = (l : B l) ^ N * z) : y = z := by
  rw [← pow_u y N, ← pow_u z N, mul_comm y, mul_comm z, h]

theorem coeff_ne (b : AInf ℂ_[l] l) (hb : b.coeff 0 ≠ 0) (h : ℕ) :
    ((WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] b).coeff 0 ≠ 0 := by
  rw [WittVector.iterate_frobenius_coeff]
  intro h0
  apply hb
  have hinj : Function.Injective (⇑(frobenius (PreTilt ↥(normInteger ℂ_[l]) l) l))^[h] :=
    Function.Injective.iterate (PerfectRing.bijective_frobenius (R := PreTilt ↥(normInteger ℂ_[l]) l)
      (p := l)).1 h
  apply hinj
  rw [iterate_frobenius, iterate_frobenius, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

theorem coeff_l_mul {n : ℕ} (hn : n ≠ 0) (b : AInf ℂ_[l] l) : ((l : AInf ℂ_[l] l) ^ n * b).coeff 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show (l : AInf ℂ_[l] l) ^ (k + 1) * b = ((l : AInf ℂ_[l] l) ^ k * b) * (l : AInf ℂ_[l] l) by ring]
  exact WittVector.mul_charP_coeff_zero _

theorem ainf_eig (h : ℕ) (m : ℤ) (hm : m ≠ 0) (x : B l) (hx : x ∈ Ainf' l) (he : Eig h m x) : x = 0 := by
  obtain ⟨a, k, rfl⟩ := mem_rep hx
  have hu : (φ l ^ h) (u l) = u l := map_u _
  set F := (WittVector.frobenius : AInf ℂ_[l] l →+* AInf ℂ_[l] l)^[h] with hF
  have he' : aB l (F a) * u l ^ k = (qB l ((l : ℚ_[l]) ^ m) * aB l a) * u l ^ k := by
    have := he
    rw [Eig, map_mul, map_pow, hu, φpow_aB] at this
    rw [this]; ring
  have e : aB l (F a) = qB l ((l : ℚ_[l]) ^ m) * aB l a := by
    have k1 : ∀ y : B l, y * u l ^ k * (l : B l) ^ k = y := fun y => by
      rw [mul_right_comm]; exact pow_u y k
    rw [← k1 (aB l (F a)), he', k1]
  have hFl : F (l : AInf ℂ_[l] l) = l := Function.iterate_fixed (map_natCast _ l) h
  have hFmul : ∀ (N : ℕ) (b : AInf ℂ_[l] l), F ((l : AInf ℂ_[l] l) ^ N * b) = (l : AInf ℂ_[l] l) ^ N * F b :=
    fun N b => by
      rw [hF, iterate_map_mul, iterate_map_pow, ← hF, hFl]
  have haB : ∀ (N : ℕ) (b : AInf ℂ_[l] l), aB l ((l : AInf ℂ_[l] l) ^ N * b) = (l : B l) ^ N * aB l b :=
    fun N b => by rw [map_mul, map_pow, map_natCast]
  suffices ha : a = 0 by rw [ha, map_zero, zero_mul]
  by_contra ha
  obtain ⟨N, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a ha
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hn : n ≠ 0 := by rintro rfl; exact hm rfl
    have e1 : (l : B l) ^ N * aB l (F b) = (l : B l) ^ N * aB l ((l : AInf ℂ_[l] l) ^ n * b) :=
      calc (l : B l) ^ N * aB l (F b) = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) := by rw [hFmul, haB]
        _ = qB l ((l : ℚ_[l]) ^ (n : ℤ)) * aB l ((l : AInf ℂ_[l] l) ^ N * b) := e
        _ = _ := by rw [zpow_natCast, map_pow, map_natCast, haB, haB]; ring
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [coeff_l_mul hn] at c
    exact coeff_ne b hb h c
  · have hn : n ≠ 0 := by rintro rfl; exact hm (by simp)
    have hq : qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * (l : B l) ^ n = 1 := by
      rw [← map_natCast (qB l) l, ← map_pow, ← map_mul, _root_.zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)), map_one]
    have e1 : (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n) = (l : B l) ^ N * aB l b :=
      calc (l : B l) ^ N * aB l (F b * (l : AInf ℂ_[l] l) ^ n)
          = aB l (F ((l : AInf ℂ_[l] l) ^ N * b)) * (l : B l) ^ n := by
            rw [hFmul, map_mul, haB, map_pow, map_natCast]; ring
        _ = qB l ((l : ℚ_[l]) ^ (-(n : ℤ))) * aB l ((l : AInf ℂ_[l] l) ^ N * b) * (l : B l) ^ n := by
            rw [e]
        _ = _ := by rw [mul_right_comm, hq, one_mul, haB]
    have e2 := aB_injective (cancel_l e1)
    have c := congrArg (fun w => WittVector.coeff w 0) e2
    rw [mul_comm, coeff_l_mul hn] at c
    exact hb c.symm

end BaseC

end period_ring_base
