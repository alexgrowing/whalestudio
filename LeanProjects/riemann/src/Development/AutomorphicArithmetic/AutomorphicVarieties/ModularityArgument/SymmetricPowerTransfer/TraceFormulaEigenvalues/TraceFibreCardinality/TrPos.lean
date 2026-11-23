import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceNil

open Module in
theorem UpperTheory.V.Z.Sym.Tf.trPos :
    UpperTheory.V.Z.Sym.Tf.TrPos := by
  intro Λ M _ _ _ u hc
  classical
  have hint := UpperTheory.V.Z.Sym.Tf.Vg_int (u := u) hc
  have hfin : {χ | UpperTheory.V.Z.Sym.Tf.Vg u χ ≠ ⊥}.Finite := by
    have := (UpperTheory.V.Z.Sym.Tf.Vg_indep hc).fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (@Finite.of_fintype _ this)
  refine ⟨hfin.toFinset, fun χ => Module.finrank ℂ (UpperTheory.V.Z.Sym.Tf.Vg u χ), ?_, ?_, ?_⟩
  · intro χ
    simp [Set.Finite.mem_toFinset, UpperTheory.V.Z.Sym.IsGenEig]
  · intro χ hχ
    rw [Set.Finite.mem_toFinset] at hχ
    exact Submodule.one_le_finrank_iff.mpr hχ
  · intro a
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (fun χ => UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have h1 : Set.MapsTo ⇑(1 : Module.End ℂ M) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) ↑(UpperTheory.V.Z.Sym.Tf.Vg u χ) :=
      fun v hv => hv
    have key := UpperTheory.V.Z.Sym.Tf.trace_Vg hc χ 1 id h1 (fun b v _ => by simp) (fun b => rfl) a
      (by simpa using UpperTheory.V.Z.Sym.Tf.Vg_maps hc a χ)
    simp only [mul_one] at key
    rw [key]
    have h2 : LinearMap.restrict (1 : Module.End ℂ M) h1 = 1 := by
      ext v
      rfl
    rw [h2, LinearMap.trace_one, mul_comm]
