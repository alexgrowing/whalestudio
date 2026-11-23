import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open NumberField

private theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem {E V : Type} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) {v : V} (hv : v ∈ Submodule.span E (L : Set V)) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : ((M * N : ℤ) : E) • (x + y) = N • ((M : E) • x) + M • ((N : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E N, ← Int.cast_smul_eq_zsmul E M ((N : E) • y), smul_smul,
        smul_smul, smul_add, Int.cast_mul, mul_comm (N : E)]
    rw [h]
    exact L.add_mem (zsmul_mem hx N) (zsmul_mem hy M)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨M, hM, hint⟩ := hc.exists_integral_multiple
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let a : 𝓞 E := ⟨M • c, hint⟩
    have ha : algebraMap (𝓞 E) E a = (M : E) * c := by
      rw [← zsmul_eq_mul]; rfl
    have h : ((M * N : ℤ) : E) • c • x = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, ha, smul_smul, smul_smul, Int.cast_mul, mul_right_comm]
    rw [h]
    exact L.smul_mem a hx

theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem :
    ∀ (I : Formalism.MainNotions.S.AutInst) (i : Fin I.n), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ Pi.single i (↑N : I.E) ∈ I.L := by
  intro I i
  obtain ⟨N, hN, h⟩ := UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem I.L
    (v := (Pi.single i (1 : I.E) : Fin I.n → I.E)) (by rw [I.L_span]; exact Submodule.mem_top)
  refine ⟨N, hN, ?_⟩
  rwa [← Pi.single_smul', smul_eq_mul, mul_one] at h
