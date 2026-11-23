import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
