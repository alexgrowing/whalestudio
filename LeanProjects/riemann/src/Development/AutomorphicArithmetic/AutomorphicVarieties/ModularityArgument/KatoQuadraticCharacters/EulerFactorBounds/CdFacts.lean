import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem cd_red (N M₀ : ℕ) [NeZero (N * M₀)] (a : ℤ) :
    (((a : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = (a : ZMod M₀) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast (dvd_mul_left M₀ N)]

private theorem cd_div (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (k : ℤ) :
    ((((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ)) : ZMod M₀) = (k : ZMod M₀) := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : (((((N : ℤ) * k : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ℤ) = k % (M₀ : ℤ) := by
    rw [Int.natCast_div, ZMod.val_intCast, Nat.cast_mul, Int.mul_emod_mul_of_pos _ _ hN,
      Int.mul_ediv_cancel_left _ hN.ne']
  rw [← Int.cast_natCast, h1, ZMod.intCast_mod]

private theorem cd_int (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (h h' : Matrix (Fin 2) (Fin 2) ℤ)
    (e : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) :
    cD N M₀ (h.map (Int.castRingHom (ZMod (N * M₀)))) = h'.map (Int.castRingHom (ZMod M₀)) := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one]
    at e00 e01 e10 e11
  have f00 : h 0 0 = h' 0 0 := mul_left_cancel₀ hN (e00.trans (mul_comm _ _))
  have f10 : h 1 0 = (N : ℤ) * h' 1 0 := e10.trans (mul_comm _ _)
  ext i j
  fin_cases i <;> fin_cases j
  · show ((((h 0 0 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 0 : ℤ) : ZMod M₀)
    rw [cd_red, f00]
  · show ((N * ((h 0 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 0 1 : ℤ) : ZMod M₀)
    rw [Nat.cast_mul, cd_red, ← e01, Int.cast_mul, Int.cast_natCast]
  · show ((((h 1 0 : ℤ) : ZMod (N * M₀)).val / N : ℕ) : ZMod M₀) = ((h' 1 0 : ℤ) : ZMod M₀)
    rw [f10, cd_div]
  · show ((((h 1 1 : ℤ) : ZMod (N * M₀)).val : ℕ) : ZMod M₀) = ((h' 1 1 : ℤ) : ZMod M₀)
    rw [cd_red, e11]

private theorem cd_lift (N M : ℕ) [NeZero M] (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (hm : ((m 1 0).val : ZMod N) = 0) :
    ∃ h h' : Matrix (Fin 2) (Fin 2) ℤ, h.map (Int.castRingHom (ZMod M)) = m ∧
      !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hm
  refine ⟨m.map fun a => (a.val : ℤ),
    !![((m 0 0).val : ℤ), N * ((m 0 1).val : ℤ); (k : ℤ), ((m 1 1).val : ℤ)], ?_, ?_⟩
  · ext i j
    show (((m i j).val : ℤ) : ZMod M) = m i j
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hk' : ((m 1 0).val : ℤ) = (k : ℤ) * N := by rw [hk]; push_cast; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one,
        Matrix.map_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue, hk', mul_comm]

private theorem cd_mul (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] (m m' : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0) :
    cD N M₀ (m * m') = cD N M₀ m * cD N M₀ m' := by
  obtain ⟨a, a', rfl, ha⟩ := cd_lift N _ m hm
  obtain ⟨b, b', rfl, hb⟩ := cd_lift N _ m' hm'
  have hab : !![(N : ℤ), 0; 0, 1] * (a * b) = (a' * b') * !![(N : ℤ), 0; 0, 1] := by
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  rw [← Matrix.map_mul, cd_int N M₀ _ _ hab, cd_int N M₀ _ _ ha, cd_int N M₀ _ _ hb, Matrix.map_mul]

private theorem cd_one (N M₀ : ℕ) [NeZero N] [NeZero (N * M₀)] :
    cD N M₀ (1 : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀))) = 1 := by
  have h := cd_int N M₀ 1 1 (by rw [Matrix.mul_one, Matrix.one_mul])
  rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)] at h

private theorem cd_inv (N M₀ : ℕ) [NeZero (N * M₀)] (m n : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))
    (e : n * m = 1) (hm : ((m 1 0).val : ZMod N) = 0) : ((n 1 0).val : ZMod N) = 0 := by
  let φ := ZMod.castHom (dvd_mul_right N M₀) (ZMod N)
  have hφ : ∀ a : ZMod (N * M₀), ((a.val : ℕ) : ZMod N) = φ a := fun a => by
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [hφ] at hm ⊢
  have e0 := congrArg φ (congrFun (congrFun e 0) 0)
  have e1 := congrArg φ (congrFun (congrFun e 1) 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul, hm] at e0 e1
  rw [Matrix.one_apply_eq, map_one] at e0
  rw [Matrix.one_apply_ne (by decide), map_zero] at e1
  linear_combination φ (n 0 0) * e1 - φ (n 1 0) * e0

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCdFacts :
    UpperTheory.V.Z.Kato.Nb.SCdFacts := by
  intro N M₀ M _ _ _ hM
  subst hM
  refine ⟨cd_mul N M₀, cd_one N M₀, ?_, cd_int N M₀⟩
  intro m hm x y hxy
  have hn := cd_inv N M₀ _ _ m.inv_mul hm
  have key : ∀ z : Row M₀, (2 : ZMod M₀) • z ≠ 0 →
      (2 : ZMod M₀) • (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) ≠ 0 := by
    intro z hz h0
    apply hz
    have h1 := congrArg (fun v => v ᵥ* cD N M₀ ((m⁻¹ : GL (Fin 2) (ZMod (N * M₀))) :
      Matrix (Fin 2) (Fin 2) (ZMod (N * M₀)))) h0
    simp only [Matrix.zero_vecMul] at h1
    rwa [Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← cd_mul N M₀ _ _ hm hn, m.mul_inv, cd_one,
      Matrix.vecMul_one] at h1
  exact ⟨key x hxy.1, key y hxy.2⟩
