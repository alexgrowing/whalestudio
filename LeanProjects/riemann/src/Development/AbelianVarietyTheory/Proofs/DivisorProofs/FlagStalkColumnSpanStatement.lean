import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStalkColumnSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_stalk_column_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N) (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y → stalkStep ι N τ l y = colSpan (g τ).1 l := by
  first | exact @GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | exact GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | (intros; apply GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan <;> assumption)
