import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_eq_span {A : Type} [CommRing A] {I : Ideal A} {t : A}
    (hI : Module.Invertible A ↥I) (h : I = Ideal.span {t}) : t ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply (Module.Invertible.toModuleEnd_bijective A ↥I).1
  rw [map_zero]
  ext ⟨y, hy⟩
  rw [h] at hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  change x * (z * t) = 0
  linear_combination z * hx

theorem hf_E_span_and_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  intro l _ K bk B g
  have h : B.I = Ideal.span {BK.hf g bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ _ _ g]
    change Ideal.map (BK.hf g) (Ideal.span {bk.E}) = _
    rw [Ideal.map_span, Set.image_singleton]
  exact ⟨h, mem_nonZeroDivisors_of_invertible_eq_span B.inv h⟩

end GlobalTheory.BSP
