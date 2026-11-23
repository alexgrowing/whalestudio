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

theorem UpperTheory.V.Z.Sym.Sig.shrink : UpperTheory.V.Z.Sym.Sig.Shrink := by
  intro k _ _ _ _ n d hd m
  set a : Fin n → ℤ := fun i => ord k (d i) with ha
  have hv : ∀ i, valuation k (d i : k) = uniformizer k ^ a i := fun i => vo (d i)
  have hlt : ∀ i j : Fin n, i < j → a j < a i := by
    intro i j hij
    have h := hd i j hij
    rw [hv, hv] at h
    exact (zpow_right_strictAnti₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).lt_iff_gt.1 h
  have hanti : Antitone a := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hlt i j h).le
    · rw [h]
  have hv' : ∀ i, valuation k ((d⁻¹) i : k) = uniformizer k ^ (-a i) := by
    intro i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, _root_.zpow_neg]
  refine ⟨fun x hx hxm => ?_, fun c y hy hym => ?_⟩
  · have hx' : x ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_N hv hanti hx, ?_⟩
    rw [GlAx.mem_Kc] at hxm ⊢
    refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hx').1 hxm d a hv ?_
    intro i j
    rcases le_or_gt j i with h | h
    · exact Or.inl fun z hz => GlAx.up_sub_one hz h
    · right
      have := hlt i j h
      push_cast
      omega
  · have hy' : y ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (c + 1) := hy
    have e1 : (dg d)⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ _).symm
    have e2 : dg d = (diagT k (Fin n) d⁻¹)⁻¹ := by
      rw [← map_inv, inv_inv]
    rw [e1, e2]
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_Nm (a := fun i => -a i) hv' (c := c) (c' := c) ?_ hy, ?_⟩
    · intro i j h
      have := hlt j i h
      omega
    · rw [GlAx.mem_Kc] at hym ⊢
      refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hy').1 hym d⁻¹
        (fun i => -a i) hv' ?_
      intro i j
      rcases le_or_gt i j with h | h
      · exact Or.inl fun z hz => GlAx.low_sub_one hz h
      · right
        have := hlt j i h
        push_cast
        omega

end
