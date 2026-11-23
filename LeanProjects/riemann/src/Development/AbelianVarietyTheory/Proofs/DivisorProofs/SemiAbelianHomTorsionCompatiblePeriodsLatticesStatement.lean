import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianHom_torsionCompatible_periods_lattices : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  first | exact @GlobalTheory.Mum.Two.periods_of_key | exact GlobalTheory.Mum.Two.periods_of_key | (intros; apply GlobalTheory.Mum.Two.periods_of_key <;> assumption)
