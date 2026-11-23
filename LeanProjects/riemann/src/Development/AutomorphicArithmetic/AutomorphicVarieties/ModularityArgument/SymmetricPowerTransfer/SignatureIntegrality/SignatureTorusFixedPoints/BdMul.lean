import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.kc_le (V : Lev k) : Kc k n (V.c + 1) ≤ V.J n := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu, t, l, hl, ht, hl', rfl⟩ := GlAx.udl _ (Ideal.pow_le_self (Nat.succ_ne_zero _)) y hy
  rw [map_mul, map_mul]
  refine mul_mem (mul_mem (V.N_le ⟨?_, u, rfl⟩) (V.TH_le (V.Tc_le_TH ⟨?_, _, ht, rfl⟩))) (V.Nm_le ⟨?_, l, hl', rfl⟩)
  · have h := (mem_unipB _).1 hu
    exact (mem_unipB _).2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩
  · refine ⟨fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i),
      fun i => (Valuation.integer.integers (valuation k)).one_of_isUnit (t i).isUnit, ?_⟩
    ext i j
    show _ = algebraMap 𝒪[k] k ((diagT _ _ t : Matrix _ _ _) i j)
    rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
    split_ifs
    · rfl
    · simp
  · have h := GlAx.mem_low.1 hl
    exact GlAx.mem_low.2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩

private theorem bd_mul {c : ℤ} {a : GL (Fin n) k} (ha : a ∈ KO k (Fin n)) (M : Matrix (Fin n) (Fin n) k)
    (hM : ∀ i j, valuation k (M i j) ≤ uniformizer k ^ c) (i j : Fin n) : valuation k ((a.val * M) i j) ≤ uniformizer k ^ c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun r _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 ha).1 i r) (hM r j)).trans_eq (one_mul _)

end

theorem UpperTheory.V.Z.Sym.Sig.memJ : UpperTheory.V.Z.Sym.Sig.MemJ := by
  intro k _ _ _ _ V n g
  rw [GlAx.unif_spec, ← zpow_natCast]
  constructor
  · intro hg
    refine ⟨GlAx.bd_zero.1 (GlAx.mem_KO.1 (V.J_le_KO hg)).1, ?_⟩
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 g hg
    have h0 : a * diagT k (Fin n) s ∈ KO k (Fin n) := mul_mem ha.2 (V.J_le_KO (V.dg_mem fun i => hs i trivial))
    have h1 := bd_mul h0 _ (GlAx.mem_Kc.1 hb.2).1
    have h2 := (mem_unipB _).1 ha.1
    have e : ∀ i j, ((a * diagT k (Fin n) s).val * (b.val - 1)) i j = (a * diagT k (Fin n) s * b).val i j - a.val i j * s j := fun i j => by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ← Units.val_mul, Units.val_mul a, val_diagT, mul_diagonal]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h1 i j
      rwa [e, h2.1 i j hij, zero_mul, sub_zero] at this
    · have h3 := h1 i i
      rw [e, h2.2, one_mul] at h3
      have h4 : valuation k (s i : k) = 1 := V.H_le (hs i trivial)
      generalize (a * diagT k (Fin n) s * b).val i i = x at h3
      have h5 : valuation k (x / s i - 1) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := by
        rw [div_sub_one (s i).ne_zero, map_div₀, h4, div_one]; exact h3
      have h6 : valuation k (x / s i) = 1 := by
        have := Valuation.map_one_add_of_lt _ (h5.trans_lt (zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega)))
        rwa [add_sub_cancel] at this
      exact ⟨Units.mk0 (x / s i) (fun h => by simp [h] at h6) * s i, mul_mem (V.le (mem_Uc.2 ⟨h6, h5⟩)) (hs i trivial), by simp⟩
  · rintro ⟨h1, h2, h3⟩
    choose s hs es using h3
    have h4 : ∀ i, valuation k (s i : k) = 1 := fun i => V.H_le (hs i)
    let U : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => if i < j then ⟨g.val i j / s j, by
      show valuation k _ ≤ 1
      rw [map_div₀, h4, div_one]; exact h1 i j⟩ else if i = j then 1 else 0
    have hU : U.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j h => by
        have h' : j < i := h
        simp [U, h'.ne', h'.le.not_gt])]
      simp [U]
    let u := GeneralLinearGroup.map (algebraMap 𝒪[k] k) (GeneralLinearGroup.mk'' U (by rw [hU]; exact isUnit_one))
    have eu : ∀ i j, u.val i j = if i < j then g.val i j / s j else if i = j then 1 else 0 := fun i j => by
      show ((U i j : 𝒪[k]) : k) = _
      simp only [U]
      split_ifs <;> rfl
    have hu : u ∈ (glIwa k n).N := ⟨(mem_unipB _).2 ⟨fun i j h => by simp [eu, h.ne', h.le.not_gt], fun i => by simp [eu]⟩, _, rfl⟩
    have h5 : u * dg s ∈ V.J n := mul_mem (V.N_le hu) (V.dg_mem hs)
    have h6 : ∀ i j, valuation k ((g.val - (u * dg s).val) i j) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := fun i j => by
      rw [Matrix.sub_apply, Units.val_mul, dg, val_diagT, mul_diagonal, eu]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h]
      · simp [es]
      · simpa [h.ne', h.le.not_gt] using h2 i j h
    have h7 : GlAx.Bd ((V.c + 1 : ℕ) : ℤ) ((u * dg s)⁻¹ * g) := fun i j => by
      have := bd_mul (V.J_le_KO (inv_mem h5)) _ h6 i j
      rwa [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel] at this
    have h8 : (u * dg s)⁻¹ * g ∈ KO k (Fin n) := by
      generalize (u * dg s)⁻¹ * g = x at h7
      have h9 := GlAx.bd_zero.1 (h7.mono (by omega))
      let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x.val i j, h9 i j⟩
      have hX : X.map (IsLocalRing.residue 𝒪[k]) = 1 := by
        ext i j
        have : X i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
          rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[k]), GlAx.mem_pow]
          have := h7.mono (show ((1 : ℕ) : ℤ) ≤ _ by omega) i j
          convert this using 2
          simp only [Matrix.sub_apply, Matrix.one_apply]
          split_ifs <;> rfl
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
        rw [map_apply, this]
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      have hd : IsUnit X.det := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hX, det_one]
        exact one_ne_zero
      exact ⟨GeneralLinearGroup.mk'' X hd, Units.ext rfl⟩
    have := mul_mem h5 (kc_le V (mem_Kc_of h8 h7))
    rwa [mul_inv_cancel_left] at this

end
