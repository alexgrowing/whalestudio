import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.HyodoDef

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def geometricCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ b : V ⊗[Qp] BdR, ∀ g, c g ⊗ₜ[Qp] (1 : BdR) = actVdR PD ρ g b - b}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def crystallineCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
    ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, map_zero _, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hxφ, hx⟩ ⟨hb, y, hyφ, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, by rw [map_add, hxφ, hyφ], fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hxφ, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, by rw [map_smul, hxφ], fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

end GlobalTheory.HyodoDef

end
