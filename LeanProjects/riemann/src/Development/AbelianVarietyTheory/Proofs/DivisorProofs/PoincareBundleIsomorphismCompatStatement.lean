import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsomorphismCompat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_bundle_isomorphism_compat : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  first | exact @GlobalTheory.KerShift.ker_shift | exact GlobalTheory.KerShift.ker_shift | (intros; apply GlobalTheory.KerShift.ker_shift <;> assumption)
