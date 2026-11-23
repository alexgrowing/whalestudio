import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem mangoldtConv_eq_of_dvd_pow {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f :=
  eq_of_monic_of_associated hg hf (hg'.associated_of_dvd hf' (hg'.prime.dvd_of_dvd_pow h))

theorem mangoldt_pow (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ f ^ m = g ^ k} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hg', k, hk, h⟩
      exact mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := m) (h ▸ dvd_pow_self g hk.ne')
    · rintro rfl
      exact ⟨hf, hf', m, hm, rfl⟩
  rw [mangoldt, this, finsum_mem_singleton]

theorem mangoldt_eq_zero (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ P = g ^ k} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hg, hg', k, hk, h'⟩
    exact h ⟨g, k, hg, hg', hk, h'⟩
  rw [mangoldt, this, finsum_mem_empty]

theorem conv_const_one_eq_divisorSum (a : F[X] → ℂ) (P : F[X]) (hP : P.Monic) :
    conv a (fun _ => 1) P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, a D := by
  unfold conv
  refine finsum_mem_eq_of_bijOn (fun x => x.1) ⟨?_, ?_, ?_⟩ ?_
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩
    exact ⟨hD, E, h.symm⟩
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩ ⟨D', E'⟩ ⟨_, _, h'⟩ h''
    simp only at h h' h'' hD
    subst h''
    rw [mul_left_cancel₀ hD.ne_zero (h.trans h'.symm)]
  · rintro D ⟨hD, E, h⟩
    exact ⟨(D, E), ⟨hD, hD.of_mul_monic_left (h ▸ hP), h.symm⟩, rfl⟩
  · intro x _
    simp

theorem mangoldtConv_finite_monicDivisors (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
  have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
  exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})

theorem mangoldt_divisorSum_mul (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by
  obtain ⟨n, R, hR, hQR⟩ := WfDvdMonoid.max_power_factor hQ.ne_zero hf'
  have hnot : f ^ (n + 1) ∉ {D : F[X] | D.Monic ∧ D ∣ Q} := by
    rintro ⟨_, h⟩
    rw [hQR, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hf.ne_zero)] at h
    exact hR h
  rw [← mangoldt_pow s f (n + 1) hf hf' n.succ_pos,
    ← finsum_mem_insert _ hnot (mangoldtConv_finite_monicDivisors Q hQ)]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext D
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Function.mem_support]
  refine and_congr_left fun hD => ?_
  constructor
  · rintro ⟨hDm, hd⟩
    obtain ⟨g, m, hg, hg', hm, rfl⟩ := not_not.mp (mt (mangoldt_eq_zero s D) hD)
    by_cases hgf : g = f
    · subst hgf
      rcases lt_trichotomy m (n + 1) with h | h | h
      · exact Or.inr ⟨hDm, hQR ▸ (pow_dvd_pow g (by omega)).mul_right R⟩
      · exact Or.inl (by rw [h])
      · exfalso
        have h2 : g ^ (n + 1) * g ∣ g ^ (n + 1) * R := by
          have h3 : g ^ (n + 1 + 1) ∣ g * Q := (pow_dvd_pow g (by omega)).trans hd
          rw [hQR, ← mul_assoc, ← pow_succ', pow_succ g (n + 1)] at h3
          exact h3
        exact hR ((mul_dvd_mul_iff_left (pow_ne_zero _ hf.ne_zero)).mp h2)
    · refine Or.inr ⟨hDm, ?_⟩
      have hc : IsCoprime g f := by
        rw [hg'.coprime_iff_not_dvd]
        intro h
        exact hgf (mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := 1) (by simpa using h))
      exact (hc.pow_left (m := m)).dvd_of_dvd_mul_left hd
  · rintro (rfl | ⟨hDm, hd⟩)
    · refine ⟨hf.pow _, ?_⟩
      rw [hQR, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
    · exact ⟨hDm, hd.mul_left f⟩

theorem IsAdditive.eq_divisorSum_mangoldt {s : F[X] → ℂ} (hs : IsAdditive s) (P : F[X]) (hP : P.Monic) :
    s P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, mangoldt s D := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hu : IsUnit P
    · have h1 : P = 1 := hP.isUnit_iff.mp hu
      subst h1
      have h0 : s 1 = 0 := by
        have := hs 1 1 monic_one monic_one
        rw [mul_one] at this
        exact left_eq_add.mp this
      rw [h0]
      symm
      refine finsum_mem_of_eqOn_zero fun D hD => ?_
      refine mangoldt_eq_zero s D ?_
      rintro ⟨g, m, _, hg', hm, rfl⟩
      exact hg'.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self g hm.ne').trans hD.2))
    · obtain ⟨f, hf, hf', Q, rfl⟩ := Polynomial.exists_monic_irreducible_factor P hu
      have hQ : Q.Monic := hf.of_mul_monic_left hP
      have hlt : Q.natDegree < n := by
        rw [← hn, hf.natDegree_mul hQ]
        have := hf'.natDegree_pos
        omega
      rw [mangoldt_divisorSum_mul s f Q hf hf' hQ, hs f Q hf hQ, ih _ hlt Q hQ rfl]

theorem mangoldt_conv_spec : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by
  intro F _ s hs
  refine ⟨fun P hP => ?_, mangoldt_pow s, mangoldt_eq_zero s⟩
  rw [conv_const_one_eq_divisorSum _ P hP]
  exact hs.eq_divisorSum_mangoldt P hP

end GlobalTheory.CuspGL
