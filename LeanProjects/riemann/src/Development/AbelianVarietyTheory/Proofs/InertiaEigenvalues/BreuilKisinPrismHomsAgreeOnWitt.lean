import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.PairW

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] {x : A}
    (h : ∀ n : ℕ, x ∈ J ^ n) : x = 0 :=
  IsHausdorff.haus' (I := J) x fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h n

theorem pow_sub_pow_mem_succ {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    {k : ℕ} (h : y - z ∈ J ^ (k + 1)) : y ^ p - z ^ p ∈ J ^ (k + 1 + 1) := by
  have h1 : y - z ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero k) h
  have hs : (∑ i ∈ Finset.range p, y ^ i * z ^ (p - 1 - i)) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hyz : Ideal.Quotient.mk J y = Ideal.Quotient.mk J z := Ideal.Quotient.eq.2 h1
    rw [map_sum]
    simp only [map_mul, map_pow, hyz]
    rw [geom_sum₂_self, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
  have e := geom_sum₂_mul y z p
  rw [← e, mul_comm, pow_succ]
  exact Ideal.mul_mem_mul h hs

theorem pow_pow_sub_mem {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    (h : y - z ∈ J) (n : ℕ) : y ^ p ^ n - z ^ p ^ n ∈ J ^ (n + 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [pow_succ p n, pow_mul, pow_mul]; exact pow_sub_pow_mem_succ p hp ih

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) (hp : (p : A) ∈ J)
    {a : ℕ} (ha : 0 < a) {y z : A} (hy : y ^ p ^ a = y) (hz : z ^ p ^ a = z) (h : y - z ∈ J) : y = z := by
  have hy' : ∀ n, y ^ p ^ (a * n) = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]
  have hz' : ∀ n, z ^ p ^ (a * n) = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  have h2 := pow_pow_sub_mem p hp h (a * n)
  rw [hy', hz'] at h2
  exact Ideal.pow_le_pow_right (Nat.le_succ_of_le (Nat.le_mul_of_pos_left n ha)) h2

theorem padicInt_ringHom_eq {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) ∈ J) (φ ψ : ℤ_[p] →+* A) (u : ℤ_[p]) : φ u = ψ u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : u = ((u.appr n : ℕ) : ℤ_[p]) + v * (p : ℤ_[p]) ^ n := by linear_combination -hv
  have e : φ u - ψ u = (φ v - ψ v) * (p : A) ^ n := by
    rw [hu]; simp only [map_add, map_mul, map_pow, map_natCast]; ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp n)

end GlobalTheory.BSP.PairW

namespace GlobalTheory.BSP

open GlobalTheory.BSP.PairW

theorem hf_C_eq_of_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  intro l _ K bk B f g w
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hI : ∀ v : Wq l bk.a, BK.hf f (C v) - BK.hf g (C v) ∈ B.I := by
    intro v
    have hr : Ideal.Quotient.mk bk.prism.I (C v : bk.prism.A) =
        bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ (C v))) :=
      (bk.str.apply_symm_apply _).symm
    rw [← Ideal.Quotient.eq]
    exact (f.f_str _ _ hr).trans (g.f_str _ _ hr).symm
  have hT : ∀ x : Fq l bk.a, BK.hf f (C (WittVector.teichmuller l x)) = BK.hf g (C (WittVector.teichmuller l x)) := by
    intro x
    have ht : (WittVector.teichmuller l x) ^ l ^ bk.a = WittVector.teichmuller l x := by
      rw [← map_pow, Fq.pow_card]
    refine eq_of_pow_eq_self (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      ?_ ?_ (Ideal.mem_sup_right (hI _))
    · rw [← map_pow, ← map_pow, ht]
    · rw [← map_pow, ← map_pow, ht]
  have hZ : ∀ u : ℤ_[l], BK.hf f (C (algebraMap ℤ_[l] (Wq l bk.a) u)) = BK.hf g (C (algebraMap ℤ_[l] (Wq l bk.a) u)) :=
    fun u => padicInt_ringHom_eq (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ
      (((BK.hf f).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (((BK.hf g).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a))) u
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact hT y
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => rw [Algebra.smul_def]; simp only [map_mul, hx, hZ]

end GlobalTheory.BSP
