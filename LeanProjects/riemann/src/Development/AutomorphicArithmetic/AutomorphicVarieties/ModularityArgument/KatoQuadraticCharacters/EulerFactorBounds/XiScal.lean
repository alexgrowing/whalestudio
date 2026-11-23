import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem xs_cast {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

private theorem xs_eval {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (k k' : ℤ_[l]) (a : X.Khat l) (h : PadicInt.toZModPow n k = PadicInt.toZModPow n k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • a - k' • a) = 0 := by
  have h1 : k - k' ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  rw [← sub_smul, map_smul]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n a)
  rw [← hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

private theorem xs_cD (N M₀ M : ℕ) [NeZero N] [NeZero M] (hM : M = N * M₀) (c : ZMod M)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (h : ((m 1 0).val : ZMod N) = 0) :
    cD N M₀ (c • m) = ((c.val : ℕ) : ZMod M₀) • cD N M₀ m := by
  have hM₀ : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have key : ∀ z : ZMod M, ((c * z).val : ZMod M₀) = (c.val : ZMod M₀) * (z.val : ZMod M₀) := by
    intro z
    rw [xs_cast hM₀, xs_cast hM₀, xs_cast hM₀, map_mul]
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h10 : (c * m 1 0).val / N = c.val * q % M₀ := by
    rw [ZMod.val_mul, hq]
    generalize c.val = cv
    rw [hM, mul_left_comm, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hN]
  have hq' : (m 1 0).val / N = q := by
    rw [hq, Nat.mul_div_cancel_left _ hN]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    ring
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, h10, hq', ZMod.natCast_mod, Nat.cast_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · simp only [cD, Matrix.smul_apply, smul_eq_mul, key, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]

private theorem xs_Cnd (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ)) (ν : (ZMod M)ˣ)
    (hν : ((ν : ZMod M).val : ZMod N) = 1) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g ((ν : ZMod M) • m) ↔ Cnd l N g m := by
  have key : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod N) = (z.val : ZMod N) := by
    intro z
    rw [xs_cast hN, xs_cast hN, map_mul, ← xs_cast hN, hν, one_mul]
  have key' : ∀ z : ZMod M, (((ν : ZMod M) * z).val : ZMod l) = ZMod.castHom hl (ZMod l) (ν : ZMod M) * (z.val : ZMod l) := by
    intro z
    rw [xs_cast hl, xs_cast hl, map_mul]
  have hu : IsUnit (ZMod.castHom hl (ZMod l) (ν : ZMod M)) := (ν.isUnit).map _
  simp only [Cnd, Matrix.smul_apply, smul_eq_mul, key, key']
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [mul_left_comm, mul_left_comm (↑(en g 0 0) : ZMod l)]
  exact hu.mul_right_inj

private theorem xs_sum {R ι A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (L : A →ₗ[R] B) (e : ι ≃ ι) (s t : Finset ι) (f g : ι → A) (h : ∀ i, i ∈ s ↔ e i ∈ t)
    (h' : ∀ i ∈ s, L (f i - g (e i)) = 0) : L (∑ i ∈ s, f i - ∑ i ∈ t, g i) = 0 := by
  rw [← Finset.sum_equiv e (t := t) (g := g) h (fun _ _ => rfl), ← Finset.sum_sub_distrib, map_sum]
  exact Finset.sum_eq_zero h'

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sXiScal :
    UpperTheory.V.Z.Kato.Nb.SXiScal := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a ν hν
  have hM := hL.eq
  have hNM : N ∣ M := ⟨M₀, hM⟩
  have hM₀M : M₀ ∣ M := ⟨N, by rw [hM, mul_comm]⟩
  have hlM₀ : l ^ n ∣ M₀ := hL.dl
  have hlM : l ∣ M := (dvd_pow_self l (by have := hL.pos; omega)).trans (hlM₀.trans hM₀M)
  have hlnM : l ^ n ∣ M := hlM₀.trans hM₀M
  let U : GL (Fin 2) (ZMod M) := Units.map (Matrix.scalar (Fin 2) : ZMod M →+* Matrix (Fin 2) (Fin 2) (ZMod M)).toMonoidHom ν
  have hU : ∀ m : GL (Fin 2) (ZMod M), ((U * m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν : ZMod M) • (m : Matrix _ _ _) := by
    intro m
    ext i j
    simp [U]
  have hdet : ∀ m : GL (Fin 2) (ZMod M), Matrix.GeneralLinearGroup.det (U * m) = ν ^ 2 * Matrix.GeneralLinearGroup.det m := by
    intro m
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hU, Matrix.det_smul, Fintype.card_fin]
  unfold CgF
  intro u
  simp only [Xi, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine xs_sum (AdicCompletion.eval (idl l) (X.Kl l) n) (Equiv.mulLeft U) _ _ _ _ ?_ ?_
  · intro m
    have hP : ν ^ 2 * Matrix.GeneralLinearGroup.det m * ν⁻¹ ^ 2 = Matrix.GeneralLinearGroup.det m := by
      rw [inv_pow, mul_right_comm, mul_inv_cancel, one_mul]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft, hU, hdet, hP, xs_Cnd l N M hNM hlM g ν hν]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp only [Equiv.coe_mulLeft, hU, hdet]
    rw [xs_cD N M₀ M hM _ _ hm.1.1, Matrix.vecMul_smul, Matrix.vecMul_smul, Matrix.smul_vecMul, Matrix.smul_vecMul]
    apply xs_eval
    simp only [map_mul, map_pow, map_add, map_natCast, Matrix.smul_apply, smul_eq_mul, xs_cast hlnM]
    rw [mul_inv, Units.val_mul, map_mul, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    have hee : ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M) * ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    set e := ZMod.castHom hlnM (ZMod (l ^ n)) (ν : ZMod M)
    set e' := ZMod.castHom hlnM (ZMod (l ^ n)) ((ν⁻¹ : (ZMod M)ˣ) : ZMod M)
    rw [mul_assoc e, mul_assoc e, ← mul_add, mul_pow]
    set D := ZMod.castHom hlnM (ZMod (l ^ n)) ((Matrix.GeneralLinearGroup.det m)⁻¹ : (ZMod M)ˣ)
    set A := ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) * PadicInt.toZModPow n (u 0) + ZMod.castHom hlnM (ZMod (l ^ n)) ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)
    linear_combination (-(e ^ w * D * A ^ w * (e * e' + 1))) * hee
