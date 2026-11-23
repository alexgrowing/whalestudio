import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix

private theorem hasTr_conj {K : Type} [Field K] {Δ : K} (γ h : DX Δ) (s : K) (hs : HasTr γ s) :
    HasTr (h⁻¹ * γ * h) s := by
  have e : Glob.mt (h⁻¹ * γ * h) = ((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) * Glob.mt γ * Glob.mt h := by
    rfl
  have e1 : Glob.mt h * (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = 1 :=
    Units.mul_inv _
  refine ⟨?_, ?_⟩
  · rw [e, det_mul_comm, ← mul_assoc, e1, one_mul, hs.1]
  · rw [e, trace_mul_comm, ← mul_assoc, e1, one_mul, hs.2]

private theorem hasTr_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (γ : DX Δ) (γ' : DX (f Δ)) (s : K)
    (h : Glob.mt γ' = (Glob.mt γ).map (lmap f Δ)) (hs : HasTr γ s) : HasTr γ' (f s) := by
  refine ⟨?_, ?_⟩
  · rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs.1, map_one]
  · rw [h, ← AddMonoidHom.map_trace, hs.2]
    ext <;> simp [lmap]

private theorem ne_zero_of_finprod {I : Type} (f : I → ℂ) (hf : (Function.mulSupport f).Finite) (h : ∏ᶠ i, f i ≠ 0) (i : I) :
    f i ≠ 0 := by
  intro h0
  apply h
  rw [finprod_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := i) ?_ h0
  simp [h0]

theorem UpperTheory.orbitalFiber_fixedSet_support :
    UpperTheory.V.Z.Sym.Glob.Fib.FSSupp := by
  intro F _ _ Δ D hD ι hι t ht γ s g hs hne v hv
  have hconj : HasTr ((g⁻¹ * ι γ * g).1 v) (cv v s) :=
    hasTr_conj ((ι γ).1 v) (g.1 v) _ (hasTr_map (cv v) γ _ s (hι γ v) hs)
  generalize g⁻¹ * ι γ * g = x at hconj hne
  have hfin : (Function.mulSupport fun w => D.fSv t w (x.1 w)).Finite := by
    have h1 : {w | ¬ x.1 w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 x.2
    refine (h1.union D.Sg.finite_toSet).subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
    apply hw
    simp only [Dat.fSv, if_neg hc.2, Glob.one, if_pos hc.1]
  have h := ne_zero_of_finprod _ hfin hne v
  simp only [Dat.fSv, if_pos hv] at h
  exact (hD.sig v hv).S_supp _ (ht v hv) _ _ hconj h
