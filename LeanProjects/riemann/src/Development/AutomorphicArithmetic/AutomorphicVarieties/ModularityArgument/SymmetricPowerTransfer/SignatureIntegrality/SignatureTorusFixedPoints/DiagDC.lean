import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem vo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : kˣ) :
    valuation k (x : k) = uniformizer k ^ ord k x := by
  have h1 := GlAx.val_div_ord x
  have h2 := GlAx.val_zpow (k := k) (ord k x)
  have e : (x : k) = ((x / unif k ^ ord k x : kˣ) : k) * ((unif k ^ ord k x : kˣ) : k) := by
    rw [← Units.val_mul, div_mul_cancel]
  rw [e, map_mul, h1, h2, one_mul]

theorem UpperTheory.V.Z.Sym.Sig.diagDC : UpperTheory.V.Z.Sym.Sig.DiagDC := by
  intro k _ _ _ _ V n d s hd
  have hlt : uniformizer k < 1 := ValuativeRel.uniformizer_lt_one
  have hpos : 0 < uniformizer k := GlAx.unif_pos
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨x1, hx1, t1, ht1, y1, hy1, rfl⟩ := (factJ k V n).1 a ha
    obtain ⟨x2, hx2, t2, ht2, y2, hy2, hb'⟩ := (factJ k V n).1 b⁻¹ (inv_mem hb)
    obtain ⟨h1, hh1, rfl⟩ := ht1
    obtain ⟨h2, hh2, rfl⟩ := ht2
    have hb2 : b = (x2 * diagT k (Fin n) h2 * y2)⁻¹ := by rw [← hb', inv_inv]
    subst hb2
    have hY0 : (diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d ∈ (glIwa k n).Nm V.c := by
      have hv : ∀ i, valuation k ((d⁻¹ i : kˣ) : k) = uniformizer k ^ (-ord k (d i)) := by
        intro i
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, vo, _root_.zpow_neg]
      have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + -ord k (d j) ≤ (V.c : ℤ) + -ord k (d i) := by
        intro i j hji
        have h0 := hd j i hji.le
        rw [vo, vo, zpow_le_zpow_iff_right_of_lt_one₀ hpos hlt] at h0
        omega
      have := GlAx.conj_Nm hv hc hy1
      rwa [map_inv, inv_inv] at this
    have hY : (diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹ ∈ (glIwa k n).Nm V.c :=
      mul_mem hY0 (inv_mem hy2)
    have hY' : diagT k (Fin n) h2 * ((diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹) *
        (diagT k (Fin n) h2)⁻¹ ∈ (glIwa k n).Nm V.c := by
      have hv : ∀ i, valuation k ((h2 i : kˣ) : k) = uniformizer k ^ ((0 : Fin n → ℤ) i) := by
        intro i
        rw [Pi.zero_apply, zpow_zero]
        exact V.H_le (hh2 i (Set.mem_univ i))
      have hc : ∀ i j : Fin n, j < i → (V.c : ℤ) + (0 : Fin n → ℤ) j ≤ (V.c : ℤ) + (0 : Fin n → ℤ) i := by
        intro i j _
        simp
      exact GlAx.conj_Nm hv hc hY
    set Y' := diagT k (Fin n) h2 * ((diagT k (Fin n) d)⁻¹ * y1 * diagT k (Fin n) d * y2⁻¹) *
        (diagT k (Fin n) h2)⁻¹ with hYq
    set T := diagT k (Fin n) (h1 * d * h2⁻¹) with hTq
    have hT : T = diagT k (Fin n) h1 * diagT k (Fin n) d * (diagT k (Fin n) h2)⁻¹ := by
      rw [hTq, map_mul, map_mul, map_inv]
    have hs : dg s = x1 * T * Y' * x2⁻¹ := by
      rw [hab, hT, hYq]
      group
    have hP1 : T⁻¹ * x1⁻¹ * T ∈ unipB k (Fin n) := by
      have := GlAx.conj_up (h1 * d * h2⁻¹)⁻¹ (inv_mem hx1.1)
      rwa [map_inv, inv_inv] at this
    have hP2 : T⁻¹ * (dg s * x2 * (dg s)⁻¹) * T ∈ unipB k (Fin n) := by
      have h0 := GlAx.conj_up s hx2.1
      have := GlAx.conj_up (h1 * d * h2⁻¹)⁻¹ h0
      rwa [map_inv, inv_inv] at this
    have hDu : diagT k (Fin n) ((h1 * d * h2⁻¹)⁻¹ * s) = T⁻¹ * dg s := by
      rw [map_mul, map_inv]
    have heq : (T⁻¹ * x1⁻¹ * T * (T⁻¹ * (dg s * x2 * (dg s)⁻¹) * T)) *
        diagT k (Fin n) ((h1 * d * h2⁻¹)⁻¹ * s) * Y'⁻¹ = 1 := by
      rw [hDu, hs]
      group
    have hu := (GlAx.uniq _ (mul_mem hP1 hP2) (inv_mem hY'.1) heq).2
    have hu1 : (h1 * d * h2⁻¹)⁻¹ * s = 1 := by
      funext i
      have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) hu
      simp only [val_diagT, diagonal_apply_eq, Units.val_one, one_apply_eq] at this
      exact Units.ext this
    have hs' : h1 * d * h2⁻¹ = s := inv_mul_eq_one.mp hu1
    intro i
    rw [← hs']
    have e : (h1 * d * h2⁻¹) i / d i = h1 i * (h2 i)⁻¹ := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (hh1 i (Set.mem_univ i)) (inv_mem (hh2 i (Set.mem_univ i)))
  · intro h
    refine ⟨1, one_mem _, diagT k (Fin n) (d⁻¹ * s), ?_, ?_⟩
    · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨d⁻¹ * s, fun i _ => ?_, rfl⟩)
      have := h i
      rwa [div_eq_mul_inv, mul_comm] at this
    · show diagT k (Fin n) s = 1 * diagT k (Fin n) d * diagT k (Fin n) (d⁻¹ * s)
      rw [one_mul, ← map_mul, mul_inv_cancel_left]

end
