import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueEmbeddingEigenspaceSum
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embedding_eigenspace_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R) (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V, (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  first | exact @GlobalTheory.EigDecomp.exists_unique_eigen_sum | exact GlobalTheory.EigDecomp.exists_unique_eigen_sum | (intros; apply GlobalTheory.EigDecomp.exists_unique_eigen_sum <;> assumption)
