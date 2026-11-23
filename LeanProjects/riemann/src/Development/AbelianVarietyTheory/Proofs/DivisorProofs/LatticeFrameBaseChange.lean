import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

namespace GlobalTheory.LieHt

theorem isFrame_latBC (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (r : ℕ) (v : Fin r → Fin m → K) (hv : IsFrame K L v) :
    IsFrame K' (latBC K' L) (fun j i => algebraMap K K' (v j i)) := by
  obtain ⟨hmem, hli, hsp⟩ := hv
  refine ⟨fun j => Submodule.subset_span ⟨v j, hmem j, rfl⟩, ?_, ?_⟩
  · exact linearIndependent_algebraMap_comp_iff.2 hli
  · have hle : latBC K' L ≤
        (Submodule.span K' (Set.range fun j i => algebraMap K K' (v j i))).restrictScalars (𝓞 K') := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp hx)
      refine (Submodule.mem_span_range_iff_exists_fun K').2 ⟨fun j => algebraMap K K' (c j), ?_⟩
      funext i
      rw [← hc]
      simp [Finset.sum_apply, Algebra.smul_def]
    intro y hy
    exact hle hy

end GlobalTheory.LieHt
