import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
