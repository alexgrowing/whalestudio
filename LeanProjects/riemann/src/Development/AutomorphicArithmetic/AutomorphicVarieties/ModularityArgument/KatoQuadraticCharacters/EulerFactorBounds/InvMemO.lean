import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem inv_mem_O {l : ℕ} [Fact l.Prime] (c : Coef l) {p : ℕ} (hp : Nat.Coprime l p) :
    ((p : Qbar l))⁻¹ ∈ c.O := by
  have hu : IsUnit (p : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hv
  rw [map_mul, map_natCast, map_one] at h
  rw [← eq_inv_of_mul_eq_one_right h]
  exact c.O.algebraMap_mem v

theorem UpperTheory.V.Z.Kato.Nb.sEulCg :
    UpperTheory.V.Z.Kato.Nb.SEulCg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ _ p n hp hn hd a δ ha hδ
  obtain ⟨k, hk⟩ := hd
  have hpk : p = l ^ n * k + 1 := by have := hp.pos; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcop : Nat.Coprime l p := by
    rw [hpk, pow_succ', mul_assoc]
    simp
  have hq := inv_mem_O cf hcop
  have hp0 : (p : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  refine ⟨?_, ?_⟩
  · unfold eul
    rw [← inv_pow, ← inv_pow]
    exact add_mem (sub_mem (one_mem _) (mul_mem ha (pow_mem hq _))) (mul_mem hδ (pow_mem hq _))
  intro σ hψ he htr hdet
  have hc : (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = p := by
    apply Subtype.val_injective
    apply (algebraMap ℚ_[l] (Qbar l)).injective
    have h : eps l σ = algebraMap ℚ_[l] (Qbar l) ((cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) : ℚ_[l]) := rfl
    rw [he] at h
    refine h.symm.trans ?_
    simp
  have hm : ((((cycMod (F := ℚ) (Ω := Ω) l 1 σ : ZMod (l ^ 1))).val : ℕ) : ZMod l) = 1 := by
    have h : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) := rfl
    rw [h, hc, map_natCast, ZMod.val_natCast, pow_one, ZMod.natCast_mod, hpk]
    simp
  have hth : thK l e ψ σ = ((p : Qbar l) ^ e)⁻¹ := by
    unfold thK
    rw [hm, hψ, he, mul_one]
  unfold rhoK at htr hdet
  rw [hth, inv_inv] at htr hdet
  rw [Matrix.trace_smul, Matrix.trace_fin_two, smul_eq_mul] at htr
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm e 2, Matrix.det_fin_two] at hdet
  have hdet' := mul_left_cancel₀ (pow_ne_zero _ hp0) hdet
  have hpc : (p : Qbar l) = (l : Qbar l) ^ (m + 1) * k + 1 := by exact_mod_cast hpk
  have ho : (k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p)) ∈ cf.O :=
    mul_mem (natCast_mem _ _) (sub_mem (mul_mem ha (pow_mem hq _))
      (mul_mem (mul_mem hδ (pow_mem hq _)) (add_mem (one_mem _) (natCast_mem _ _))))
  have key : eul l e p a δ - 1 * (mat W σ - 1).det =
      (l : Qbar l) ^ (m + 1) * ((k : Qbar l) * (a * (p : Qbar l)⁻¹ ^ (e + 1) - δ * (p : Qbar l)⁻¹ ^ 2 * (1 + p))) := by
    rw [← mul_assoc, ← sub_eq_of_eq_add hpc, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero]
    unfold eul
    rw [← htr, ← hdet']
    simp only [inv_pow]
    field_simp
    ring
  unfold GlobalTheory.Ord2.Cg
  rw [key, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (nle cf ho)
