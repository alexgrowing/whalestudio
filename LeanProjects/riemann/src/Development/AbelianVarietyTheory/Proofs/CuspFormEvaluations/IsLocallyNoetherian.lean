import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace UnivPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def pol (Xo : Moduli D l) : PolAV Xo.X := GlobalTheory.Obj.toPolAV Xo.univ

@[simp] theorem pol_A (Xo : Moduli D l) : (pol Xo).A = Xo.univ.t.G := rfl

@[simp] theorem pol_L (Xo : Moduli D l) : (pol Xo).L = Xo.univ.t.PP.L := rfl

@[simp] theorem pol_g (Xo : Moduli D l) : (pol Xo).g = Module.finrank ℚ E / 2 * (D.p + D.q) := rfl

theorem smooth (Xo : Moduli D l) : Smooth Xo.s :=
  haveI := Xo.smooth
  SmoothOfRelativeDimension.smooth D.dim Xo.s

theorem isLocallyNoetherian (Xo : Moduli D l) : IsLocallyNoetherian Xo.X := by
  haveI := smooth Xo
  exact LocallyOfFiniteType.isLocallyNoetherian Xo.s

theorem isReduced (Xo : Moduli D l) : IsReduced Xo.X := by
  haveI := smooth Xo
  exact GlobalTheory.isReduced_of_smooth_of_isReduced Xo.s

theorem isUnit_natCast (Xo : Moduli D l) (n : ℕ) (hn : 0 < n) : IsUnit (n : Γ(Xo.X, ⊤)) := by
  have hK : IsUnit (n : KA l) := by
    haveI : CharZero (KA l) := (RingHom.charZero_iff (algebraMap (KA l) ℂ).injective).2 inferInstance
    exact (isUnit_iff_ne_zero).2 (Nat.cast_ne_zero.2 hn.ne')
  have hΓ := hK.map ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv.hom)
  have hX := hΓ.map Xo.s.appTop.hom
  simpa using hX

end UnivPol

theorem moduli_univ_polAV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), IsLocallyNoetherian Xo.X ∧ IsReduced Xo.X ∧ (∀ n : ℕ, 0 < n → IsUnit (n : Γ(Xo.X, ⊤))) ∧ IsAbelianScheme Xo.univ.t.G ∧ ∀ (p : ∀ (A : Over Xo.X) [GrpObj A] [IsCommMonObj A], LB A.left → ℕ → Prop), (∀ P : PolAV Xo.X, p P.A P.L P.g) → p Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l Xo
  exact ⟨UnivPol.isLocallyNoetherian Xo, UnivPol.isReduced Xo, UnivPol.isUnit_natCast Xo,
    ObjDim.isAbelianScheme Xo.univ, fun p h => h (UnivPol.pol Xo)⟩

end GlobalTheory
