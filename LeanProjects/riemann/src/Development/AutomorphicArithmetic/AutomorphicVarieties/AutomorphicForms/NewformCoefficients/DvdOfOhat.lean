import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.MemMirabIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem dvd_of_ohat {M : ℕ} (hM : 1 ≤ M) (n : ℤ) {y : Af ℚ} (hy : y ∈ Ohat ℚ)
    (h : (n : Af ℚ) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have e : algebraMap ℚ (Af ℚ) ((n : ℚ) / M) = y := by
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹) * (M : Af ℚ) = 1 := by
      rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
    rw [div_eq_inv_mul, map_mul, map_intCast, h, ← mul_assoc, h1, one_mul]
  obtain ⟨m, hm⟩ := ratAd.2.2 _ (e ▸ hy)
  refine ⟨m, ?_⟩
  have : (n : ℚ) = M * m := by rw [← hm]; field_simp
  exact_mod_cast this

private theorem part1 {M : ℕ} (hM : 1 ≤ M) (γ : GL (Fin 2) ℚ) (hγ : toF γ ∈ K1G M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      ((toR γ).val = δ.1.map (Int.cast : ℤ → ℝ) ∨ (toR γ).val = eps * δ.1.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨h1, h2, ⟨y, hy, h3⟩, z, hz, h4⟩ := (memK M _).1 hγ
  rw [← map_inv] at h2
  choose A hA using fun a b => ratAd.2.2 (γ a b) (h1 a b)
  choose B hB using fun a b => ratAd.2.2 ((γ⁻¹ : GL (Fin 2) ℚ) a b) (h2 a b)
  have hA' : γ.val = (Matrix.of A).map (Int.castRingHom ℚ) := Matrix.ext hA
  have hB' : (γ⁻¹).val = (Matrix.of B).map (Int.castRingHom ℚ) := Matrix.ext hB
  have hdet : (Matrix.of A).det * (Matrix.of B).det = 1 := by
    have : γ.val.det * (γ⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [hA', hB', ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at this
    simp only [eq_intCast] at this
    exact_mod_cast this
  have hc : (M : ℤ) ∣ A 1 0 := by
    refine dvd_of_ohat hM _ hy ?_
    rw [← h3, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hd : (M : ℤ) ∣ A 1 1 - 1 := by
    refine dvd_of_ohat hM _ hz ?_
    rw [← h4, Int.cast_sub, Int.cast_one, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hc' : ((A 1 0 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
  have hd' : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    push_cast at this
    exact sub_eq_zero.1 this
  have hR : ∀ a b, (toR γ).val a b = (A a b : ℝ) := fun a b => by
    show Rat.castHom ℝ (γ a b) = _
    rw [hA]; simp
  have key : ∀ δ : SL(2, ℤ), δ 1 0 = A 1 0 → δ 1 1 = A 1 1 → δ ∈ Gamma1 M := by
    intro δ e1 e2
    rw [Gamma1_mem, e1, e2]
    refine ⟨?_, hd', hc'⟩
    have := congrArg (Int.cast : ℤ → ZMod M) δ.det_coe
    rw [Matrix.det_fin_two] at this
    push_cast at this
    change ((δ 0 0 : ℤ) : ZMod M) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (δ 1 0 : ℤ) = 1 at this
    rw [e1, e2, hc', hd'] at this
    simpa using this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
  · refine ⟨⟨Matrix.of A, h⟩, key _ rfl rfl, Or.inl (Matrix.ext hR)⟩
  · refine ⟨⟨!![-A 0 0, -A 0 1; A 1 0, A 1 1], ?_⟩, key _ rfl rfl, Or.inr ?_⟩
    · rw [Matrix.det_fin_two] at h
      simp only [Matrix.of_apply] at h
      rw [Matrix.det_fin_two_of]; linear_combination -h
    · ext a b
      rw [hR]
      fin_cases a <;> fin_cases b <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

private theorem part2 {M : ℕ} (hM : 1 ≤ M) (u : (Af ℚ)ˣ) (hu : IsZU u) :
    ∃ (δ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ), δ ∈ Gamma0 M ∧ γ.val = δ.1.map (Int.cast : ℤ → ℚ) ∧
      (toF γ)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G M ∧
      ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = M * y := by
  obtain ⟨d, y, hy, hd⟩ := ratAd.2.1 M hM _ hu.1
  obtain ⟨e, z, hz, he⟩ := ratAd.2.1 M hM _ hu.2
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have huu : (u : Af ℚ) * (u⁻¹ : (Af ℚ)ˣ) = 1 := u.mul_inv
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ e * d - 1 := by
    refine dvd_of_ohat hM _ (y := -(z * u + e * y)) (neg_mem (add_mem (mul_mem hz hu.1) (mul_mem (hI e) hy))) ?_
    push_cast
    linear_combination (-(u : Af ℚ)) * he - (e : Af ℚ) * hd + huu
  let δ : SL(2, ℤ) := ⟨!![e, t; M, d], by rw [Matrix.det_fin_two_of]; linear_combination ht⟩
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -M := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = e := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  refine ⟨δ, Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, rfl, (memK M _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-u, neg_mem hu.1, ?_⟩,
    -(z * u), neg_mem (mul_mem hz hu.1), ?_⟩, y, hy, hd⟩
  · rw [Gamma0_mem]; simp [δ]
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10]; push_cast; ring
  · rw [e1, i11]; linear_combination (-(u : Af ℚ)) * he + huu

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratK :
    UpperTheory.V.Af.Nf.RatK := fun _ hM =>
  ⟨fun γ hγ => UpperTheory.V.Af.Nf.part1 hM γ hγ, fun u hu => UpperTheory.V.Af.Nf.part2 hM u hu⟩
