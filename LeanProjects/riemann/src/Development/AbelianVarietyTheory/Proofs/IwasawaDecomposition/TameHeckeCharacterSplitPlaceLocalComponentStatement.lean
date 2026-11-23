import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
open NumberField IsDedekindDomain Formalism.L2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_heckeCharacter_split_place_local_component : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  first | exact @GlobalTheory.HeckeSplitComp.main | exact GlobalTheory.HeckeSplitComp.main | (intros; apply GlobalTheory.HeckeSplitComp.main <;> assumption)
