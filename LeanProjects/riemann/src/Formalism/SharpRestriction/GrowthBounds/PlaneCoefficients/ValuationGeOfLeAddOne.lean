import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

section Gen

variable {σ R : Type*} [CommRing R]

theorem X_mul_mono (v : σ) (mo : σ →₀ ℕ) (c : R) : X v * monomial mo c = monomial (mo + Finsupp.single v 1) c := by
  rw [X, monomial_mul, one_mul, add_comm]

theorem eul_mono (w : σ) (L : σ →₀ ℕ) (c : R) : X w * pderiv w (monomial L c) = monomial L (c * (L w : R)) := by
  rw [X_mul_pderiv_monomial, smul_monomial, nsmul_eq_mul, mul_comm]

theorem pderiv_add_single (w : σ) (L : σ →₀ ℕ) (c : R) :
    pderiv w (monomial (L + Finsupp.single w 1) c) = monomial L (c * ((L w : R) + 1)) := by
  rw [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  push_cast
  rfl

theorem pderiv_mono_zero (w : σ) (L : σ →₀ ℕ) (c : R) (h : L w = 0) : pderiv w (monomial L c) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (w : σ) (L : σ →₀ ℕ) (h : L w ≠ 0) : ∃ L', L = L' + Finsupp.single w 1 := ⟨L - Finsupp.single w 1,
  (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩

end Gen

theorem stepA {P e : ℕ} (hP : 0 < P) (h : e % P + 1 < P) : (e + 1) % P = e % P + 1 ∧ (e + 1) / P = e / P := by
  obtain ⟨h1, h2⟩ := (Nat.div_mod_unique (a := e + 1) (d := e / P) (c := e % P + 1) hP).mpr
    ⟨by have := Nat.mod_add_div e P; linarith, h⟩
  exact ⟨h2, h1⟩

theorem stepB {P e : ℕ} (hP : 0 < P) (h : e % P + 1 = P) : (e + 1) % P = 0 ∧ (e + 1) / P = e / P + 1 := by
  obtain ⟨h1, h2⟩ := (Nat.div_mod_unique (a := e + 1) (d := e / P + 1) (c := 0) hP).mpr
    ⟨by rw [mul_add, mul_one]; have := Nat.mod_add_div e P; linarith, hP⟩
  exact ⟨h2, h1⟩

section PolS

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem multideg_add_single (mo : ι × Fin n →₀ ℕ) (x0 : ι) (a : Fin n) (i : ι) :
    multideg (mo + Finsupp.single (x0, a) 1) i = multideg mo i + if i = x0 then 1 else 0 := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = x0
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mem_Pol' {d : ι → ℕ} {F : MvPolynomial (ι × Fin n) R} :
    F ∈ Pol R n d ↔ ∀ m ∈ F.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    exact h hm
  · intro h m hm
    exact h m hm

theorem mono_mem_Pol {d : ι → ℕ} (m : ι × Fin n →₀ ℕ) (c : R) (h : ∀ i, multideg m i = d i) :
    monomial m c ∈ Pol R n d := by
  rw [mem_Pol']
  intro m' hm'
  have h1 := support_monomial_subset hm'
  rw [Finset.mem_singleton] at h1
  rw [h1]
  exact h

theorem Pol_pderiv {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d' x0 = d x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : pderiv (x0, a) H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hz : m (x0, a) = 0
  · rw [pderiv_mono_zero _ _ _ hz]
    exact Submodule.zero_mem _
  · obtain ⟨m', rfl⟩ := exists_add_single _ m hz
    rw [pderiv_add_single]
    apply mono_mem_Pol
    intro i
    have hi := hH _ hm i
    rw [multideg_add_single] at hi
    by_cases hix : i = x0
    · subst hix
      simp at hi
      omega
    · simp [hix] at hi
      rw [hi, h1 i hix]

theorem Pol_X_mul {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = d' x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : X (x0, a) * H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [X_mul_mono]
  apply mono_mem_Pol
  intro i
  rw [multideg_add_single, hH m hm i]
  by_cases hix : i = x0
  · subst hix
    simp
    omega
  · simp [hix]
    exact h1 i hix

theorem pderiv_eq_zero_of_deg {d : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = 0)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d) : pderiv (x0, a) H = 0 := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  apply pderiv_mono_zero
  have h1 := hH m hm x0
  rw [h0] at h1
  unfold multideg at h1
  exact (Finset.sum_eq_zero_iff.mp h1) a (Finset.mem_univ a)

end PolS

theorem valuation_ge_of_le_add_one {x y : WithTop ℤ} {t t' : ℝ} (h : x ≤ y + ((1 : ℤ) : WithTop ℤ)) (hx : geZ x t') (ht : t + 1 ≤ t') :
    geZ y t := by
  intro k hk
  rw [hk] at h
  have h' : x ≤ ((k + 1 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_add]
    exact h
  induction x using WithTop.recTopCoe with
  | top => simp at h'
  | coe k'' =>
    have h2 := hx k'' rfl
    have h3 : (k'' : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast WithTop.coe_le_coe.mp h'
    linarith

section ValOp

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem val_der (G : MvPolynomial (ι × Fin n) Kf) (w : ι × Fin n) {t t' : ℝ} (h0 : t ≤ t')
    (h1 : w.1 ∈ S → LL.vec w.1 = true → t + 1 ≤ t') (hG : geZ (valS LL S G) t') : geZ (valS LL S (pderiv w G)) t := by
  have geZ_mono : ∀ {x y : WithTop ℤ} {s s' : ℝ}, x ≤ y → geZ x s' → s ≤ s' → geZ y s := by
    intro x y s s' hxy hx hss k hk
    rw [hk] at hxy
    induction x using WithTop.recTopCoe with
    | top => simp at hxy
    | coe k'' =>
      have h2 := hx k'' rfl
      have h3 : (k'' : ℝ) ≤ (k : ℝ) := by exact_mod_cast WithTop.coe_le_coe.mp hxy
      linarith
  by_cases hc : w.1 ∈ S ∧ LL.vec w.1 = true
  · exact valuation_ge_of_le_add_one (valS_pderiv (LL := LL) (S := S) G w) hG (h1 hc.1 hc.2)
  · have hv : w.1 ∈ S → LL.vec w.1 = false := fun hs =>
      Bool.eq_false_iff.mpr (fun hv => hc ⟨hs, hv⟩)
    exact geZ_mono (valS_pderiv_of (LL := LL) (S := S) G w hv) hG h0

theorem val_mul (G : MvPolynomial (ι × Fin n) Kf) (w : ι × Fin n) {t t' : ℝ} (h0 : t ≤ t')
    (h1 : w.1 ∈ S → LL.vec w.1 = false → t + 1 ≤ t') (hG : geZ (valS LL S G) t') : geZ (valS LL S (X w * G)) t := by
  have geZ_mono : ∀ {x y : WithTop ℤ} {s s' : ℝ}, x ≤ y → geZ x s' → s ≤ s' → geZ y s := by
    intro x y s s' hxy hx hss k hk
    rw [hk] at hxy
    induction x using WithTop.recTopCoe with
    | top => simp at hxy
    | coe k'' =>
      have h2 := hx k'' rfl
      have h3 : (k'' : ℝ) ≤ (k : ℝ) := by exact_mod_cast WithTop.coe_le_coe.mp hxy
      linarith
  by_cases hc : w.1 ∈ S ∧ LL.vec w.1 = false
  · exact valuation_ge_of_le_add_one (valS_X_mul (LL := LL) (S := S) G w) hG (h1 hc.1 hc.2)
  · have hv : w.1 ∈ S → LL.vec w.1 = true := fun hs =>
      by
        cases hb : LL.vec w.1
        · exact absurd ⟨hs, hb⟩ hc
        · rfl
    exact geZ_mono (valS_X_mul_of (LL := LL) (S := S) G w hv) hG h0

end ValOp

end Formalism.MainNotions.PairMembershipBlocks
