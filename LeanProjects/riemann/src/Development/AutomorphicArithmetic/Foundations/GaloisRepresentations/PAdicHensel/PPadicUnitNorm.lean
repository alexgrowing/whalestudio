import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma UpperTheory.Gal.G1.normInt_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (h : ¬ (q : ℤ) ∣ n) :
    ‖(n : ℤ_[q])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((PadicInt.norm_int_lt_one_iff_dvd n).mp hlt))

private lemma UpperTheory.Gal.G1.norm_lt_one_iff_toZMod {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma UpperTheory.Gal.G1.norm_eq_one_of_toZMod {q : ℕ} [Fact q.Prime] {x : ℤ_[q]}
    (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod x).mp hlt))

private lemma UpperTheory.Gal.G1.hens {q : ℕ} [Fact q.Prime] (c d a : ℤ_[q]) (h2 : ‖(2 : ℤ_[q])‖ = 1)
    (hc : ‖c‖ = 1) (ha : ‖a‖ = 1) (h : ‖c * a ^ 2 + d‖ < 1) : ∃ z : ℤ_[q], c * z ^ 2 + d = 0 := by
  let F : Polynomial ℤ_[q] := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d
  have hF : ∀ t, Polynomial.aeval t F = c * t ^ 2 + d := by
    intro t; simp [F]
  have hF' : ∀ t, Polynomial.aeval t (Polynomial.derivative F) = c * (2 * t) := by
    intro t
    simp [F]
    exact Or.inl (Or.inl one_add_one_eq_two)
  have hn : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [hF', norm_mul, norm_mul, hc, h2, ha]; simp
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hn, hF]; simpa using h)
  exact ⟨z, by rwa [hF] at hz⟩

theorem UpperTheory.Gal.G1.pPadicUnitNorm :
    PadicUnitNorm := by
  intro q _ D hqD u hu
  have hq2 : ¬ (q : ℤ) ∣ 2 := fun h => hqD (Dvd.dvd.mul_right h D)
  have hqd : ¬ (q : ℤ) ∣ D := fun h => hqD (Dvd.dvd.mul_left h 2)
  have h2 : ‖(2 : ℤ_[q])‖ = 1 := by
    have := UpperTheory.Gal.G1.normInt_eq_one (q := q) hq2
    simpa using this
  have hD : ‖(D : ℤ_[q])‖ = 1 := UpperTheory.Gal.G1.normInt_eq_one hqd
  have hodd : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : q.Prime).eq_two_or_odd with h | h
    · subst h; exact absurd (by norm_num) hq2
    · exact h
  let U : ℤ_[q] := ⟨u, hu.le⟩
  have hU : ‖U‖ = 1 := hu
  have hUc : ((U : ℤ_[q]) : ℚ_[q]) = u := rfl
  have hub : PadicInt.toZMod U ≠ 0 := fun h0 =>
    absurd hU ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod U).mpr h0).ne
  have hDb : -(D : ZMod q) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hqd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2)
    (g := Polynomial.C (-(D : ZMod q)) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X
      + Polynomial.C (-PadicInt.toZMod U))
    (by simp) (Polynomial.degree_quadratic hDb) hodd
  have hab' : a ^ 2 - (D : ZMod q) * b ^ 2 - PadicInt.toZMod U = 0 := by
    simp at hab
    linear_combination hab
  let x0 : ℤ_[q] := (a.val : ℤ_[q])
  let y0 : ℤ_[q] := (b.val : ℤ_[q])
  have hx : PadicInt.toZMod x0 = a := by simp [x0]
  have hy : PadicInt.toZMod y0 = b := by simp [y0]
  have hDz : PadicInt.toZMod (D : ℤ_[q]) = (D : ZMod q) := by simp
  have key : ‖x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U‖ < 1 := by
    rw [UpperTheory.Gal.G1.norm_lt_one_iff_toZMod]
    simp only [map_sub, map_mul, map_pow, hx, hy, hDz]
    exact hab'
  have hor : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    apply hub
    rw [ha0, hb0] at hab'
    simpa using hab'
  rcases hor with ha | hb
  · have hx1 : ‖x0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hx])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens 1 (-((D : ℤ_[q]) * y0 ^ 2 + U)) x0 h2 (by simp) hx1 (by
      have e : 1 * x0 ^ 2 + -((D : ℤ_[q]) * y0 ^ 2 + U) = x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U := by ring
      rw [e]; exact key)
    refine ⟨z, y0, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination -h3
  · have hy1 : ‖y0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hy])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens (D : ℤ_[q]) (U - x0 ^ 2) y0 h2 hD hy1 (by
      have e : (D : ℤ_[q]) * y0 ^ 2 + (U - x0 ^ 2) = -(x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U) := by ring
      rw [e, norm_neg]; exact key)
    refine ⟨x0, z, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination h3
