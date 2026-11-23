import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.AdmissibleDesigns.AdmG5OfAdm51AdmG5
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPointStatement

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem splitCase_bound_at_point_of_admitted_items : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
    (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
    EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB := by
  intro hAR hTD hEC D i r ρ π dc ep e' c0 cB hA hG2 hL hD hπ
  obtain ⟨hJ, hRow⟩ := EmbeddingTypes.jump_and_length_of_admitted i r ρ π dc e' c0 cB hA hL hD hπ
  obtain ⟨g1, -, g3, g4, g578, g5x, g6, -, a51, -, -, hBK, hLc, -, -, hTB, unr, ct, -, dcm, -, tie, -,
    font, -, fin, -⟩ := hA
  have g5 : TruncatedSeriesCountingIdentities.admG5 i r := Formalism.MainNotions.N.K.SplitLatticeDiagonal.admG5_of_adm51_admG5 i r ρ π hπ a51 g578
  have g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π := hG2 hL.2.2.2.1 hL.2.2.2.2 hπ
  refine ⟨hJ, hRow, fun hs hsha _ => ?_⟩
  have hthm := GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces hAR hTD hEC D i r ρ π dc (EmbeddingTypes.lenRowSplit i dc e' c0) (fun _ => e') cB
    g1 g2 g3 g4 g5 g5x g6 hBK.1 hBK.2 ct dcm font fin tie a51 unr
    (EmbeddingTypes.admissible_length_of_local i r ρ π dc hD.2 e' c0 hRow) hLc hTB
  exact EmbeddingTypes.length_bound_of_theorem i ρ π dc hD.2 e' c0 cB hJ hthm hL.2.2.2.1 hL.2.2.2.2 hπ hs hsha

end GlobalTheory
