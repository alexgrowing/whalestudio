import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem dg_mat (k : ℕ) (hk : 0 < k) :
    (((dg k : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![(k : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  have hdet : 0 < (!![(k : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two_of]
    exact_mod_cast hk
  simp only [dg, toGQ, dif_pos hdet]
  rfl

private theorem ofSL_mat (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl

private theorem eOm_zero' {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  have h : Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ)) = ε 1 := by simp
  unfold eOm
  rw [h]
  exact Function.leftInverse_invFun ε.injective 1

theorem galDg : GalDg := by
  intro Ω _ _ _ ε X k hk
  have hinj : Function.Injective X.exp := X.exp.toRingHom.injective
  have hD : ∀ (f : X.K) (q : ℚ), (X.exp (X.sl (dg k) f)).coeff q = (X.exp f).coeff (q / k) := by
    intro f q
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have h := X.exp_upper (dg k) (by simp [ent, dg_mat k hk]) f (q / k)
    have e00 : ent (dg k) 0 0 = k := by simp [ent, dg_mat k hk]
    have e01 : ent (dg k) 0 1 = 0 := by simp [ent, dg_mat k hk]
    have e11 : ent (dg k) 1 1 = 1 := by simp [ent, dg_mat k hk]
    rw [e00, e01, e11] at h
    simpa [hkq, eOm_zero'] using h
  refine ⟨fun s f => hinj ?_, fun γ γ' h f => ?_, ?_⟩
  · ext q
    rw [X.gal_exp, hD, hD, X.gal_exp]
  · have hm : dg k * ofSL γ = ofSL γ' * dg k := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [dg_mat k hk, ofSL_mat, ofSL_mat, ← Matrix.map_mul, ← Matrix.map_mul, h]
    rw [← X.sl_mul, ← X.sl_mul, hm]
  · intro M γ
    induction γ using Matrix.SpecialLinearGroup.fin_two_induction with
    | _ a b c d hdet => ?_
    intro hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
    change ((a : ℤ) : ZMod (k * M)) = 1 at h00
    change ((b : ℤ) : ZMod (k * M)) = 0 at h01
    change ((c : ℤ) : ZMod (k * M)) = 0 at h10
    change ((d : ℤ) : ZMod (k * M)) = 1 at h11
    have hb := (ZMod.intCast_zmod_eq_zero_iff_dvd b _).mp h01
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd c _).mp h10
    have ha := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 a (k * M)).mp (by rw [Int.cast_one]; exact h00.symm)
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 d (k * M)).mp (by rw [Int.cast_one]; exact h11.symm)
    push_cast at ha hb hc hd
    have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    obtain ⟨c', rfl⟩ : (k : ℤ) ∣ c := dvd_trans (dvd_mul_right _ _) hc
    have hc' : (M : ℤ) ∣ c' := (mul_dvd_mul_iff_left hkz).mp hc
    have hdet' : a * d - (k * b) * c' = 1 := by rw [← hdet]; ring
    refine ⟨⟨!![a, k * b; c', d], by rw [Matrix.det_fin_two_of]; exact hdet'⟩, ?_, ?_⟩
    · refine CongruenceSubgroup.Gamma_mem.mpr ⟨?_, ?_, ?_, ?_⟩
      · change ((a : ℤ) : ZMod M) = 1
        rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (dvd_trans (dvd_mul_left _ _) ha)
      · change ((k * b : ℤ) : ZMod M) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact (dvd_trans (dvd_mul_left _ _) hb).mul_left _
      · change ((c' : ℤ) : ZMod M) = 0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hc'
      · change ((d : ℤ) : ZMod M) = 1
        rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (dvd_trans (dvd_mul_left _ _) hd)
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end UpperTheory.V.Z.Kato.Sym

end
