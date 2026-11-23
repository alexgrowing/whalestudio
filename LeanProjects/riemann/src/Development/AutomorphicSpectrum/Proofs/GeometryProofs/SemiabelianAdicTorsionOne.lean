import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfMain
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_hopf_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La), ∃ (U : ∀ n, (X.Γ n).G.left.Opens) (H : ∀ n, Subgroup (LevGrp La p n)), (∀ n, (X.Γ n).IsFinOpenSub (U n)) ∧ (∀ n (g : (X.Γ n).G.left), (X.Γ n).G.hom g = IsLocalRing.closedPoint O → g ∈ U n) ∧ (∀ n t, t ∈ H n ↔ ∀ z, ((X.Γ n).pt t).left z ∈ U n) ∧ (∀ n, IsHopfOrder ((X.Γ n).btOrder ⊤)) ∧ (∀ n, IsHopfOrder (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n, (X.Γ n).btOrder ⊤ = indOrder (H n).subtype (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n (a : La), lev p n a ∈ H n ↔ lev p (n + 1) (p • a) ∈ H (n + 1)) ∧ ∀ n (a : La), lev p n a ∈ H n → ∃ b : La, lev p (n + 1) b ∈ H (n + 1) ∧ lev p n b = lev p n a :=
  PositivityTheory.HtPt.Twhopf.tw_hopf

end GlobalTheory.CompanionTheory.Ar.HT
