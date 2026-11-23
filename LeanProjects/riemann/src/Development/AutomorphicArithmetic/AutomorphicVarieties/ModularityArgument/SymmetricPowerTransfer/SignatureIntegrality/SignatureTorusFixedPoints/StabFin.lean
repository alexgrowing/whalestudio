import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.stabFin : UpperTheory.V.Z.Sym.Sig.StabFin := by
  intro k _ _ _ _ V n y
  obtain ⟨a, ha⟩ := GlAx.exists_bd y
  obtain ⟨b, hb⟩ := GlAx.exists_bd y⁻¹
  have big : ∀ (g : GL (Fin n) k) (a : ℕ), GlAx.Bd (-a) g → ∀ i j, valuation k (g.val i j) ≤ uniformizer k ^ (-a : ℤ) := fun g a h i j => by
    have e : g.val i j = (g.val - 1) i j + (1 : Matrix (Fin n) (Fin n) k) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ (h i j) ?_
    rw [one_apply]
    split_ifs
    · rw [map_one, ← zpow_zero (uniformizer k)]; exact GlAx.zpow_le (by omega)
    · simp
  have key : ∀ u : Fin n → kˣ, (∀ i, u i ∈ Uc k (V.c + 1 + a + b)) → GlAx.Bd ((V.c + 1 : ℕ) : ℤ) (y⁻¹ * dg u * y) := fun u hu i j => by
    have e : (y⁻¹ * dg u * y).val - 1 = (y⁻¹).val * ((dg u).val - 1) * y.val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul y⁻¹ y, inv_mul_cancel]; rfl
    rw [e, Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Valuation.map_sum_le _ fun q _ => ?_
    rw [map_mul, map_mul]
    refine (mul_le_mul' (mul_le_mul' (big _ b hb i q) ((GlAx.mem_Kc.1 (dg_mem_Kc.2 hu)).1 q r)) (big _ a ha r j)).trans_eq ?_
    rw [← zpow_add₀ GlAx.unif_pos.ne', ← zpow_add₀ GlAx.unif_pos.ne']
    congr 1; push_cast; ring
  refine ⟨V.c + 1 + a + b, fun u hu => ?_⟩
  have h : y⁻¹ * dg u * y ∈ Kc k n (V.c + 1) := GlAx.mem_Kc.2 ⟨key u hu, by
    have := key u⁻¹ fun i => inv_mem (hu i)
    rw [dg, map_inv] at this
    convert this using 1; group⟩
  have h1 := (GlAx.mem_Kc.1 h).1
  have h0 := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le _ h)).1
  generalize y⁻¹ * dg u * y = g at h h1 h0
  refine (memJ k V n g).2 ⟨h0, fun i j hij => ?_, fun i => ?_⟩
  · have := h1 i j
    rw [Matrix.sub_apply, one_apply_ne hij.ne', sub_zero, zpow_natCast] at this
    rwa [GlAx.unif_spec]
  · have := h1 i i
    rw [Matrix.sub_apply, one_apply_eq] at this
    have h2 : valuation k (g.val i i - 1) < 1 := this.trans_lt (zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega))
    have h3 : valuation k (g.val i i) = 1 := by
      have := Valuation.map_one_add_of_lt _ h2
      rwa [add_sub_cancel] at this
    exact ⟨Units.mk0 _ (fun h => by simp [h] at h3), V.le (mem_Uc.2 ⟨h3, this⟩), rfl⟩

end
