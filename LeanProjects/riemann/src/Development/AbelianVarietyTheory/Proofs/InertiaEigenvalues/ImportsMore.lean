import Mathlib

namespace GlobalTheory.AbelianStatement

open Module

theorem main {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
    [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]
    {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W] [Module (PowerSeries k) W]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) W]
    (f : W →ₗ[LaurentSeries k] V) {N : Submodule (PowerSeries k) V} (hN : N.FG) :
    ∃ (m : ℕ) (b : Fin m → V),
      LinearIndependent (LaurentSeries k)
        ((⇑(Submodule.mkQ (LinearMap.range f)) : V → V ⧸ LinearMap.range f) ∘ b) ∧
      ∀ y ∈ N, ∃ (a : Fin m → PowerSeries k) (x : W),
        (f : W → V) x ∈ N ∧ y = ∑ j : Fin m, a j • b j + (f : W → V) x := by
  classical
  let π : V →ₗ[PowerSeries k] (V ⧸ LinearMap.range f) :=
    (LinearMap.range f).mkQ.restrictScalars (PowerSeries k)
  let P : Submodule (PowerSeries k) (V ⧸ LinearMap.range f) := N.map π
  haveI : Module.Finite (PowerSeries k) P := Module.Finite.iff_fg.mpr (hN.map π)
  haveI : FaithfulSMul (PowerSeries k) (LaurentSeries k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  haveI : IsTorsionFree (PowerSeries k) (V ⧸ LinearMap.range f) :=
    IsTorsionFree.trans_faithfulSMul (PowerSeries k) (LaurentSeries k) _
  haveI : IsTorsionFree (PowerSeries k) P := inferInstance
  let B := Module.finBasis (PowerSeries k) P
  have hB : ∀ j, ∃ v ∈ N, π v = (B j : V ⧸ LinearMap.range f) := fun j => (B j).2
  choose b hbN hb using hB
  refine ⟨_, b, ?_, ?_⟩
  · have e : ((LinearMap.range f).mkQ : V → V ⧸ LinearMap.range f) ∘ b
        = (Subtype.val : P → V ⧸ LinearMap.range f) ∘ B := by
      funext j; exact hb j
    rw [e, ← LinearIndependent.iff_fractionRing (PowerSeries k) (LaurentSeries k)]
    exact B.linearIndependent.map' P.subtype (Submodule.ker_subtype _)
  · intro y hy
    have hyP : π y ∈ P := Submodule.mem_map_of_mem hy
    set c := B.repr ⟨π y, hyP⟩ with hc
    have hsum := congrArg Subtype.val (B.sum_repr ⟨π y, hyP⟩)
    have h0 : π (y - ∑ j, c j • b j) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hb]
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      rw [hsum, sub_self]
    have hz : y - ∑ j, c j • b j ∈ LinearMap.range f := (Submodule.Quotient.mk_eq_zero _).mp h0
    obtain ⟨x, hx⟩ := hz
    refine ⟨c, x, ?_, ?_⟩
    · rw [hx]; exact N.sub_mem hy (N.sum_mem fun j _ => N.smul_mem _ (hbN j))
    · rw [hx]; abel

end GlobalTheory.AbelianStatement
