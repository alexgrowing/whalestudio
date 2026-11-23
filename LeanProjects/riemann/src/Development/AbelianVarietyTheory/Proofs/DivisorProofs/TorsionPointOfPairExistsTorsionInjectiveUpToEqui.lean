import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem torsPt_exists_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D : DegData R J) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif J D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → (∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x ∧ x ^ k = 1) ∧ ∀ (p p' : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x → QkPt.Equiv D.toPre F p p' := by
  intro R _ _ _ J hJ D A G _ _ U hG F _ _ _ k hk
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.exists_tors_closed R J hJ D A G hG U F k hk
  refine ⟨fun p => ⟨f p, (hf.1 p (f p)).2 rfl, ?_⟩, fun p p' x h h' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · exact (hf.2.2.1 p p').1 (((hf.1 p x).1 h).symm.trans ((hf.1 p' x).1 h'))

end GlobalTheory.TInj
