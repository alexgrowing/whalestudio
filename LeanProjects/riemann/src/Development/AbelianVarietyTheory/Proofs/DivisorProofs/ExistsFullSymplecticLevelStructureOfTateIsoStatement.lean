import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  first | exact @GlobalTheory.FullLevel.exists_sympLevel_of_tate | exact GlobalTheory.FullLevel.exists_sympLevel_of_tate | (intros; apply GlobalTheory.FullLevel.exists_sympLevel_of_tate <;> assumption)
