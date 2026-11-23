import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Per.AmbFil

theorem filCount_at (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {n : ℕ}
    (M : Br.G D.nbr i w hw →* Matrix (Fin n) (Fin n) ↥C.LL.1) :
    EmbeddingTypes.FilCount (Br.PD D.loc D.nbr i w hw) (matRep M) := by
  intro τ J hJ
  exact GlobalTheory.Per.FilCount.fil_count (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL _ (matRep M) τ J hJ

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  intro D i r ρ π dc
  exact ⟨fun w hw _ C x => filCount_at D i w hw C _,
    fun _ => ⟨fun w hw _ C => filCount_at D i w hw C _, fun w hw _ C => filCount_at D i w hw C _⟩⟩

end GlobalTheory.Per.AmbFil
