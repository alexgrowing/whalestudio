import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem IsChowForm.exists_pderiv_ne_zero {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    {g : MvPolynomial (Fin (k + 1) × Fin n) F} (hg : IsChowForm P (k + 1) g) :
    ∃ l, pderiv (0, l) g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ v, pderiv v g = 0 := by
    rintro ⟨i, l⟩
    obtain ⟨c, hc2, hc⟩ := hg.rename_swap 0 i
    have hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n)) :=
      (Equiv.swap 0 i).injective.prodMap Function.injective_id
    have h := pderiv_rename hinj (0, l) g
    rw [hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    exact (mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)

  have hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v := by
    intro s hs v
    by_cases h0 : s v = 0
    · simp [h0]
    have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    have h1 := congrArg (coeff (s - Finsupp.single v 1)) (hall v)
    rw [coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h2
    have h3 : ((s v : ℕ) : F) = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      push_cast
      exact h2
    exact (CharP.cast_eq_zero_iff F p _).1 h3

  obtain ⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by
    have hroot : ∀ a : F, ∃ b : F, b ^ p = a := fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    choose r hr using hroot
    refine ⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (coeff s g)), ?_⟩
    rw [sum_pow_char]
    conv_rhs => rw [as_sum g]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s := by
      ext v
      simp [Nat.mul_div_cancel' (hexp s hs v)]
    rw [monomial_pow, hr, hs']

  have hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q := by
    intro q
    rw [← hg.2 q, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have hI := IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant
    have hspan : incIdeal P (k + 1) = Ideal.span {g} := by
      ext q
      rw [Ideal.mem_span_singleton, hmem]
    rw [hspan] at hI
    exact (Ideal.span_singleton_prime hg.1).1 hI
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])
  obtain ⟨q, hq⟩ := hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have h1 : h * (h ^ (m + 1) * q) = h * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq, ← hgh, hm]
    ring
  have hu : IsUnit (h ^ (m + 1)) := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)
  have hu' : IsUnit h := (isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu
  exact hprime.not_isUnit (hgh ▸ hu'.pow p)

theorem ChowFormBirationalAlgClosed.proof : ChowFormBirationalAlgClosed.Statement := by
  intro F _ _ n k P g c hP hg hc
  obtain _ | ⟨p, hp, hch⟩ := CharP.exists' F
  · exact ChowFormBirational.full F n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩

  obtain ⟨l, hl⟩ := IsChowForm.exists_pderiv_ne_zero (p := p) hP hg
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
