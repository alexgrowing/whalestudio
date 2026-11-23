import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsFieldExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  first | exact @GlobalTheory.VarFlag.rel_baseChange | exact GlobalTheory.VarFlag.rel_baseChange | (intros; apply GlobalTheory.VarFlag.rel_baseChange <;> assumption)
