import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.Coisotropic

theorem eq_one_of_unitOn_eq_one {R : Type} [CommRing R] {u : Rˣ} (h : unitOn u = 1) : u = 1 := by
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact congrArg Units.val h

theorem level_dvd_form_of_cubWeil_one : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), ∀ (K : Type) [Field K] [IsAlgClosed K] (u : Sp K ⟶ U) (a a' : D.La) (p p' : Over.mk (u ≫ j) ⟶ t.G), p.left = u ≫ (o.etaA a).left ≫ μ₀.φ → p'.left = u ≫ (o.etaA a').left ≫ μ₀.φ → CubWeil t.cub l.A p p' 1 → (l.A : ℤ) ∣ D.EF a a' := by
  intro hL E _ _ _ H D l B _ b X U j s o t μ₀ K _ _ u a a' p p' hp hp' h
  have hβ : u ≫ s = spMap (Spec.preimage (u ≫ s)).hom := (Spec.map_preimage (u ≫ s)).symm
  obtain ⟨-, I, -, hI, -⟩ := o.geom K u _ hβ
  have hA : IsAbelianScheme o.t.G := ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩
  have kill : ∀ c, I.ev l.A c ^ l.A = 1 := fun c => (I.onto l.A l.A_pos _).2 ⟨c, rfl⟩
  have h₁ : CubWeil o.t.cub l.A (I.ev l.A a) (I.ev l.A a') (unitOn (I.ζ l.A ^ D.EF a a')) :=
    (cubWeil_iff_weilIs hL.globalFns hA (kill a) (kill a') _).2 (I.isom l.A l.A_pos a a')
  have h₂ := GlobalTheory.T.cubicalBundlePairing_compatible_pullback X U j t.G o.t.G μ₀.cm μ₀.cart.1.w
    (fun T x y => Over.OverMorphism.ext (μ₀.cart.2 T x y _ _ rfl rfl).symm) _ _ _ _ μ₀.lin l.A _ _ _ _ h₁
  have e : ∀ (c : D.La) (q : Over.mk (u ≫ j) ⟶ t.G), q.left = u ≫ (o.etaA c).left ≫ μ₀.φ →
      Out.toBase μ₀.cart.1.w (I.ev l.A c) = q := fun c q hq => Over.OverMorphism.ext (by
    rw [hq, ← hI c]
    show ((toUnit (Over.mk u)).left ≫ (o.etaA c).left) ≫ μ₀.φ = _
    rw [Category.assoc]
    rfl)
  rw [e a p hp, e a' p' hp'] at h₂
  exact ((I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd _).1 (eq_one_of_unitOn_eq_one (h₂.unique h))

end GlobalTheory.Coisotropic
