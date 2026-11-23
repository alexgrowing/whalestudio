import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLatticeIndexBaseChangePow
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_lattice_index_base_change_pow : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)) (r : ℕ) (v : Fin r → Fin m → K), L.FG → IsFrame K L v → (Submodule.span (𝓞 K') (Set.range fun j i => algebraMap K K' (v j i))).toAddSubgroup.relIndex (latBC K' L).toAddSubgroup = (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ^ Module.finrank K K' := by
  first | exact @GlobalTheory.LatBCIdx.relIndex_span_latBC | exact GlobalTheory.LatBCIdx.relIndex_span_latBC | (intros; apply GlobalTheory.LatBCIdx.relIndex_span_latBC <;> assumption)
