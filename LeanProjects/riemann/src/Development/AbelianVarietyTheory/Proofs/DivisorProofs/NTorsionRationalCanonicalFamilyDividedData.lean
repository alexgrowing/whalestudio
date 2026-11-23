import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionGaloisFixedCanonicalNDividedFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torsRat_of_canon : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → TorsRat G n := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hu ζ hζ Q e hD hQB G _ _ P hC
  haveI : CharZero R := hCN.2.2.2
  have hfix := GlobalTheory.T.torsion_galoisFixed_canonical_nDivided_family T R iw s ε n hCN hn hu ζ hζ Q e hD hQB G P hC
  obtain ⟨_, D', F, A', G', _, _, U', oA, oG, inc, pr, _, _, hinc, hpr, hip, _, _⟩ := hC
  exact GlobalTheory.T.torsionRational_of_retract_galoisFixed_points G G' A' U'.gen inc pr n U'.gen_hom hinc hpr hip hn hfix

end GlobalTheory.Mum
