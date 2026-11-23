import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelCoverUniformisationDictionary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelCover_uniformisation_dictionary : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ), d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ → ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r), ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  first | exact @GlobalTheory.CoverUnif.exists_unf_dict | exact GlobalTheory.CoverUnif.exists_unf_dict | (intros; apply GlobalTheory.CoverUnif.exists_unf_dict <;> assumption)
