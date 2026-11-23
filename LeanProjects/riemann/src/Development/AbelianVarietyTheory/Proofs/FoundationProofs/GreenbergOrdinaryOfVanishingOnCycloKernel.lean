import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GrOfKill

theorem exists_unit_one_add (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by
  have hu : IsUnit (((1 + l : ℕ) : ℤ_[l])) := by
    push_cast
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  exact ⟨hu.unit, rfl⟩

theorem gr_of_vanish_on_trivial : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), (∀ g ∈ N0g W, y g = 0) → Gr W A y := by
  intro l _ Ω _ _ _ e S A W hW y hy hN
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have hmul : ∀ s t, mat W (s * t) = mat W s * mat W t := fun s t => by simp [mat]
  have hone : mat W 1 = 1 := by simp [mat]
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup t ht]; ring
  have h11 : ∀ s t, s ∈ D → mat W (s * t) 1 1 = mat W s 1 1 * mat W t 1 1 := by
    intro s t hs; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, hup s hs]; ring
  have h01 : ∀ s t, t ∈ D → mat W (s * t) 0 1 = mat W s 0 0 * mat W t 0 1 + mat W s 0 1 * mat W t 1 1 := by
    intro s t ht; rw [hmul, Matrix.mul_apply, Fin.sum_univ_two]
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t := fun s t => by
    have := hy.2 s t
    rw [this]; rfl
  have hy1 : y 1 = 0 := by
    have := hcoc 1 1
    simpa [hone] using this
  have hb : ∀ s t, s ∈ D → y (s * t) 1 = y s 1 + mat W s 1 1 * y t 1 := by
    intro s t hs; rw [hcoc]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hup s hs]

  let P : G ℚ Ω → Prop := fun u => u ∈ D ∧ mat W u 0 0 = 1 ∧ mat W u 1 1 = 1 ∧ cycBar ℚ Ω l u = 1

  have hfac : ∀ u v, P u → P v → mat W u 0 1 = mat W v 0 1 → y u = y v := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩ h
    have hm : mat W u = mat W v := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hu0, hv0]
      · exact h
      · simp [hup u huD, hup v hvD]
      · simp [hu1, hv1]
    have hW' : W u = W v := Units.ext hm
    have hn : u⁻¹ * v ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · simp [MonoidHom.mem_ker, map_mul, map_inv, huc, hvc]
      · simp [MonoidHom.mem_ker, map_mul, map_inv, hW']
    have e1 : v = u * (u⁻¹ * v) := by group
    rw [e1, hcoc, hN _ hn, Matrix.mulVec_zero, add_zero]
  have hPmul : ∀ u v, P u → P v → P (u * v) ∧ mat W (u * v) 0 1 = mat W u 0 1 + mat W v 0 1 ∧
      y (u * v) 1 = y u 1 + y v 1 := by
    rintro u v ⟨huD, hu0, hu1, huc⟩ ⟨hvD, hv0, hv1, hvc⟩
    refine ⟨⟨D.mul_mem huD hvD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 u v hvD, hu0, hv0, one_mul]
    · rw [h11 u v huD, hu1, hv1, one_mul]
    · rw [map_mul, huc, hvc, one_mul]
    · rw [h01 u v hvD, hu0, hv1]; ring
    · rw [hb u v huD, hu1, one_mul]
  have hPpow : ∀ u, P u → ∀ n : ℕ, P (u ^ n) ∧ mat W (u ^ n) 0 1 = n * mat W u 0 1 ∧
      y (u ^ n) 1 = n * y u 1 := by
    intro u hu n
    induction n with
    | zero =>
      refine ⟨⟨D.one_mem, by simp [hone], by simp [hone], by simp⟩, by simp [hone], by simp [hy1]⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := hPmul _ _ ih.1 hu
      rw [pow_succ]
      refine ⟨h1, ?_, ?_⟩
      · rw [h2, ih.2.1]; push_cast; ring
      · rw [h3, ih.2.2]; push_cast; ring

  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ n : ℕ, mat W (s ^ n) 0 0 = mat W s 0 0 ^ n := by
    intro s hs n
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  set T := t ^ (2 * m) with hTdef
  have hTD : T ∈ D := D.pow_mem htD _
  set Nq : ℕ := (1 + l) ^ (2 * (e * m)) with hNq
  have hT00 : mat W T 0 0 = (Nq : Qbar l) := by
    rw [hTdef, hpow00 t htD, pow_mul', hm t htI, heps, hNq]; push_cast; ring
  have hdet : mat W T 0 0 * mat W T 1 1 = 1 := by
    have h2 : dt W t ^ 2 = 1 := by
      have := congrArg (fun f => f t) hW.det2
      simpa using this
    have hdT : dt W T = 1 := by
      rw [hTdef, map_pow, pow_mul, h2, one_pow]
    have h3 : ((dt W T : (Qbar l)ˣ) : Qbar l) = (mat W T).det := rfl
    rw [hdT, Units.val_one, Matrix.det_fin_two, hup T hTD] at h3
    linear_combination -h3
  have hNqne : ∀ k : ℕ, 1 ≤ k → ((Nq ^ k : ℕ) : Qbar l) ≠ 1 := by
    intro k hk h
    have h' : Nq ^ k = 1 := by exact_mod_cast h
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hpos : 2 * (e * m) ≠ 0 := by
      have := hW.e_pos; positivity
    have : 1 < Nq ^ k := by
      rw [hNq, ← pow_mul]
      exact Nat.one_lt_pow (by positivity) (by omega)
    omega
  have hTi : T * T⁻¹ = 1 := mul_inv_cancel T
  have hTiD : T⁻¹ ∈ D := D.inv_mem hTD
  have hTi11 : mat W T⁻¹ 1 1 = (Nq : Qbar l) := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone] at this
    rw [Matrix.one_apply_eq] at this
    linear_combination (-(mat W T⁻¹ 1 1)) * hdet - (mat W T 0 0) * this + hT00
  have hi11 : mat W T 1 1 * mat W T⁻¹ 1 1 = 1 := by
    have := h11 T T⁻¹ hTD
    rw [hTi, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinvy : y T 1 + mat W T 1 1 * y T⁻¹ 1 = 0 := by
    have := hb T T⁻¹ hTD
    rw [hTi, hy1] at this
    simpa using this.symm

  have hPconj : ∀ u, P u → P (T * u * T⁻¹) ∧ mat W (T * u * T⁻¹) 0 1 = ((Nq * Nq : ℕ) : Qbar l) * mat W u 0 1 ∧
      y (T * u * T⁻¹) 1 = mat W T 1 1 * y u 1 := by
    rintro u ⟨huD, hu0', hu1, huc⟩
    have hTuD : T * u ∈ D := D.mul_mem hTD huD
    have hi00 : mat W T 0 0 * mat W T⁻¹ 0 0 = 1 := by
      have := h00 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_eq] at this
      exact this.symm
    have hi01 : mat W T 0 0 * mat W T⁻¹ 0 1 + mat W T 0 1 * mat W T⁻¹ 1 1 = 0 := by
      have := h01 T T⁻¹ hTiD
      rw [hTi, hone, Matrix.one_apply_ne (by decide)] at this
      exact this.symm
    refine ⟨⟨D.mul_mem hTuD hTiD, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [h00 _ _ hTiD, h00 _ _ huD, hu0', mul_one, hi00]
    · rw [h11 _ _ hTuD, h11 _ _ hTD, hu1, mul_one, hi11]
    · simp [map_mul, map_inv, huc]
    · rw [h01 _ _ hTiD, h01 _ _ huD, h00 _ _ huD, hu0', hu1]
      push_cast
      linear_combination hi01 + mat W u 0 1 * mat W T⁻¹ 1 1 * hT00 + mat W u 0 1 * (Nq : Qbar l) * hTi11
    · rw [mul_assoc, hb T _ hTD, hb u T⁻¹ huD, hu1]
      linear_combination hinvy

  have hvan : ∀ u, P u → y u 1 = 0 := by
    intro u hu
    obtain ⟨hc1, hc2, hc3⟩ := hPconj u hu
    obtain ⟨hp1, hp2, hp3⟩ := hPpow u hu (Nq * Nq)
    have h3 := hfac _ _ hc1 hp1 (by rw [hc2, hp2])
    have h4 : mat W T 1 1 * y u 1 = ((Nq * Nq : ℕ) : Qbar l) * y u 1 := by rw [← hc3, ← hp3, h3]
    have h5 : (((Nq ^ 3 : ℕ) : Qbar l) - 1) * y u 1 = 0 := by
      push_cast at h4 ⊢
      linear_combination (-(Nq : Qbar l)) * h4 + y u 1 * hdet - y u 1 * mat W T 1 1 * hT00
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (sub_eq_zero.1 h) (hNqne 3 (by norm_num))
    · exact h

  have hT11ne : mat W T 1 1 - 1 ≠ 0 := by
    intro h
    have h' : mat W T 1 1 = 1 := sub_eq_zero.1 h
    rw [h', mul_one, hT00] at hdet
    exact hNqne 1 (by norm_num) (by simpa using hdet)
  refine ⟨y T 1 / (mat W T 1 1 - 1), fun s hs => ?_⟩
  have hsT : s * T ∈ D := D.mul_mem hs hTD
  have hTs : T * s ∈ D := D.mul_mem hTD hs
  have hsTi : (s * T)⁻¹ ∈ D := D.inv_mem hsT
  have hinv00 : mat W (s * T)⁻¹ 0 0 * mat W (s * T) 0 0 = 1 := by
    have := h00 (s * T)⁻¹ (s * T) hsT
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hinv11 : mat W (s * T)⁻¹ 1 1 * mat W (s * T) 1 1 = 1 := by
    have := h11 (s * T)⁻¹ (s * T) hsTi
    rw [inv_mul_cancel, hone, Matrix.one_apply_eq] at this
    exact this.symm
  have hcP : P ((s * T)⁻¹ * (T * s)) := by
    refine ⟨D.mul_mem hsTi hTs, ?_, ?_, ?_⟩
    · rw [h00 _ _ hTs, h00 _ _ hs]
      linear_combination hinv00 - mat W (s * T)⁻¹ 0 0 * h00 s T hTD
    · rw [h11 _ _ hsTi, h11 _ _ hTD]
      linear_combination hinv11 - mat W (s * T)⁻¹ 1 1 * h11 s T hs
    · have hcs : cycBar ℚ Ω l (T * s) = cycBar ℚ Ω l (s * T) := by rw [map_mul, map_mul, mul_comm]
      rw [map_mul, map_inv, hcs, inv_mul_cancel]
  have hyc := hvan _ hcP
  have e1 : (s * T) * ((s * T)⁻¹ * (T * s)) = T * s := by group
  have h6 := hb (s * T) ((s * T)⁻¹ * (T * s)) hsT
  rw [e1, hyc, mul_zero, add_zero, hb T s hTD, hb s T hs] at h6
  have hinv := mul_inv_cancel₀ hT11ne
  rw [div_eq_mul_inv]
  linear_combination (mat W T 1 1 - 1)⁻¹ * h6 - y s 1 * hinv

end GlobalTheory.Ord2.GrOfKill
