import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_coeff_deltaOK_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0) (p : ℕ) (I : Ideal (𝓞 E)), CoverOK d p I → RootOK d → (∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ) → ∃ φ : ∀ n, (Fin n → LevQ Dw d.l₂) → c.F, ∀ n, DeltaOK (GlobalTheory.FormTies.withCoeff d (φ n)) p I := by
  intro E _ _ _ H Dw l Xo c d p I hc hr ⟨ψ, hψ, ht⟩
  have key : ∀ n, ∃ φ : (Fin n → LevQ Dw d.l₂) → c.F, DeltaOK (GlobalTheory.FormTies.withCoeff d φ) p I := by
    intro n
    by_cases hn : Dw.p + Dw.q ≤ n
    · obtain ⟨φ, ph, x₀, h⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n
        (GlobalTheory.FormTies.withCoeff d (0 : (Fin n → LevQ Dw d.l₂) → c.F)) hc.2.2.1 hn ψ
      exact ⟨φ, hc, hr, fun _ => ⟨ph, ψ, x₀, hψ, h, ht⟩⟩
    · exact ⟨0, hc, hr, fun h => absurd h hn⟩
  choose φ hφ using key
  exact ⟨φ, hφ⟩

end GlobalTheory
