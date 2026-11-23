import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatioAgreeOnOverlap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_agree_on_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) st (V V' : Z.X.Opens) (A B : Γ(Z.X, V)) (A' B' : Γ(Z.X, V')), IsAffineOpen (V ⊓ V') → RatioAt Z st V ![A] ![B] → RatioAt Z st V' ![A'] ![B'] → ∃ u : Γ(Z.X, V ⊓ V')ˣ, u.val * ((Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom A' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom B) = (Z.X.presheaf.map (homOfLE (inf_le_right : V ⊓ V' ≤ V')).op).hom B' * (Z.X.presheaf.map (homOfLE (inf_le_left : V ⊓ V' ≤ V)).op).hom A := by
  first | exact @GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit | exact GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit | (intros; apply GlobalTheory.HTLine.Overlap.ratioAt_overlap_unit <;> assumption)
