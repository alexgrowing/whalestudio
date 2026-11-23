import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitOrth

theorem place_mul_place {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from FiniteAdeleRing.ext _ fun w => ?_)
  change evalV D.host.F w (α * β) = evalV D.host.F w 0
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem split_mul_split : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' hv
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h1 : q.e * q.e = q.e := q.split.1
  have h2 : q.e * cA D q.e = 0 := q.split.2.1
  have h1' : q'.e * q'.e = q'.e := q'.split.1
  have h2' : q'.e * cA D q'.e = 0 := q'.split.2.1
  have a : q.e = q.e * algebraMap _ _ ε := by rw [← he, mul_add, h1, h2, add_zero]
  have a' : q'.e = q'.e * algebraMap _ _ ε' := by rw [← he', mul_add, h1', h2', add_zero]
  rw [a, a', mul_mul_mul_comm, ← map_mul, place_mul_place hε hε' hv, map_zero, mul_zero]

end GlobalTheory.SplitOrth
