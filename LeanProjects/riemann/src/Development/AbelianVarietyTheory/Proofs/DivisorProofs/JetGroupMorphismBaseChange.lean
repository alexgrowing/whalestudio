import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem JetRing.π_algebraMap {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (r : R) :
    J.π (algebraMap R J.B r) = r := by
  rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self]
  simp

theorem isBC_jetRing : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC := by
  intro _ H _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X m
  have e : (𝟙 _ : Sp R ⟶ Sp R) = spMap (RingHom.id R) := (Cris.spMap_id R).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl X.A).congr e rfl
  have key : ∀ (t : Sp R ⟶ Sp R), t = spMap (RingHom.id R) →
      ∀ m : GrpMor (dp0 R) t X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift H X.ab X.dim (isDPNilpotent_bot R) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h J.nil
      (fun r ↦ ⟨_, J.π_algebraMap r⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl X.A)
  exact key _ e m

end GlobalTheory.LatJet
