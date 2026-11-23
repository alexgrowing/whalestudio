import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.law_of_squares_selfDual_splitLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n r : ℕ), Odd r → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)), (⟨L⟩ : GenLat E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) → cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc → ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm cc : ℚ) := by
  first | exact @GlobalTheory.LawOfSquares.law_of_squares | exact GlobalTheory.LawOfSquares.law_of_squares | (intros; apply GlobalTheory.LawOfSquares.law_of_squares <;> assumption)
