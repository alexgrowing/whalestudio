import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_element_iwasawa_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ g : GLoc σ J v, ∃ p : siegelH (Fv F v) σ (dblGram finSumFinEquiv J), ∃ k ∈ KFin σ (dblGram finSumFinEquiv J) L v, ioH (Fv F v) σ rfl (g, 1) = (p : GLoc σ (dblGram finSumFinEquiv J) v) * k := by
  first | exact @GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | exact GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin | (intros; apply GlobalTheory.InertIwasawaGen.ioH_mem_siegel_mul_KFin <;> assumption)
