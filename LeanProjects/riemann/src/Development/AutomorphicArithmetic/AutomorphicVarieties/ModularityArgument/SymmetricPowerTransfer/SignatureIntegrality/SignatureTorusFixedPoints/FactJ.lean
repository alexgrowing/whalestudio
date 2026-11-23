import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.factJ : UpperTheory.V.Z.Sym.Sig.FactJ := by
  intro k _ _ _ _ V n
  constructor
  · have hm : ∀ {a b : GL (Fin n) k}, (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y) →
        (∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, b = x * t * y) →
        ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a * b = x * t * y := by
      rintro _ _ ⟨x, hx, t, ht, y, hy, rfl⟩ ⟨x', hx', t', ht', y', hy', rfl⟩
      obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := (glIwa k n).swap V.c y hy x' hx'
      refine ⟨x * (t * x2 * t⁻¹), mul_mem hx ((glIwa k n).T_N t (V.levelTorus_le_torus ht) x2 hx2), t * s * t',
        mul_mem (mul_mem ht (V.Tc_le_TH hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
        mul_mem ((glIwa k n).T_Nm V.c t'⁻¹ (inv_mem (V.levelTorus_le_torus ht')) y2 hy2) hy', ?_⟩
      calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
        _ = _ := by rw [h]; group
    have h1 : ∀ a ∈ (glIwa k n).N, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨a, ha, 1, one_mem _, 1, one_mem _, by simp⟩
    have h2 : ∀ a ∈ V.TH n, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, a, ha, 1, one_mem _, by simp⟩
    have h3 : ∀ a ∈ (glIwa k n).Nm V.c, ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, a = x * t * y :=
      fun a ha => ⟨1, one_mem _, 1, one_mem _, a, ha, by simp⟩
    let K : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ∃ x ∈ (glIwa k n).N, ∃ t ∈ V.TH n, ∃ y ∈ (glIwa k n).Nm V.c, g = x * t * y}
        mul_mem' := hm
        one_mem' := h1 1 (one_mem _)
        inv_mem' := by
          rintro _ ⟨x, hx, t, ht, y, hy, rfl⟩
          have := hm (h3 _ (inv_mem hy)) (hm (h2 _ (inv_mem ht)) (h1 _ (inv_mem hx)))
          simpa only [_root_.mul_inv_rev, Set.mem_setOf_eq] using this }
    exact fun g hg => (show V.J n ≤ K from sup_le (sup_le h1 h2) h3) hg
  · rintro m a ha a' ha' _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ b hb b' hb' h
    have hT : ∀ s : Fin n → kˣ, (∀ i, s i ∈ V.H) → dg s ∈ KO k (Fin n) := fun s h => V.J_le_KO (V.dg_mem h)
    have k1 := Kc_conj (mul_mem (hT s' fun i => hs' i trivial) (V.J_le_KO (V.Nm_le hb'))) h
    set κ := dg s' * b' * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ with hκ
    set l := dg s * (b * b'⁻¹) * (dg s')⁻¹ with hl
    have e : a⁻¹ * a' = l * κ := by
      have : l * κ = dg s * b * ((a * diagT k (Fin n) s * b)⁻¹ * (a' * diagT k (Fin n) s' * b')) * (dg s' * b')⁻¹ := by
        rw [hl, hκ]; group
      rw [this]; group
    have hl0 : l ∈ KO k (Fin n) := mul_mem (mul_mem (hT s fun i => hs i trivial) (V.J_le_KO (V.Nm_le (mul_mem hb (inv_mem hb')))))
      (inv_mem (hT s' fun i => hs' i trivial))
    have hl1 : ∀ i j, i < j → (l : Matrix (Fin n) (Fin n) k) i j = 0 := fun i j hij => by
      rw [hl, dg, dg, ← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul,
        (GlAx.mem_low.1 (mul_mem hb (inv_mem hb')).1).1 i j hij]
      simp
    have hu := mul_mem (inv_mem ha) ha'
    refine mem_Kc_of hu.2 fun i j => ?_
    rcases le_or_gt j i with hij | hij
    · rw [GlAx.up_sub_one hu.1 hij]; simp
    · have e2 : ((a⁻¹ * a').val - 1) i j = ∑ r, l.val i r * (κ.val - 1) r j := by
        rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, hl1 i j hij, one_apply_ne hij.ne, e,
          Units.val_mul]
      rw [e2]
      refine Valuation.map_sum_le _ fun r _ => ?_
      rw [map_mul]
      exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 hl0).1 i r) ((GlAx.mem_Kc.1 k1).1 r j)).trans_eq (one_mul _)

end
