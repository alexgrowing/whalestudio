import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  first | exact @GlobalTheory.USepGen.genfib_pull | exact GlobalTheory.USepGen.genfib_pull | (intros; apply GlobalTheory.USepGen.genfib_pull <;> assumption)
