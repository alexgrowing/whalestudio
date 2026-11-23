import Formalism.LocalToGlobal.ProjectiveLattices.GenValInjPf

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def SepXSt : Prop := IsSeparated Xo.s

def LocDomSt : Prop := ∀ P : Xo.XF c, IsDomain ((Xo.XF c).presheaf.stalk P)

def stkAlg (P : Xo.XF c) : Algebra c.F ((Xo.XF c).presheaf.stalk P) :=
  (Spec.preimage ((Xo.XF c).fromSpecStalk P ≫ strK)).hom.toAlgebra

def xStk (P : Xo.XF c) : Sp ((Xo.XF c).presheaf.stalk P) ⟶ Xo.X :=
  (Xo.XF c).fromSpecStalk P ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

def LocFrSt : Prop :=
  ∀ P : Xo.XF c, letI := stkAlg Xo c P; ∃ y : FrPt Xo c ((Xo.XF c).presheaf.stalk P), y.x = xStk Xo c P

variable {Xo c}

variable (Xo c) in

def FrGenChartSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω) (κ : Om Z →ₐ[c.F] Ω) (γ : q.R →ₐ[c.F] Ω)
        (w w₀ : FrPt Xo c Ω) (t : Ix Dw → Ωˣ),
        Function.Injective γ ∧ FrMap γ yq w ∧ FrMap κ (genFr hG Z) w₀ ∧ FrBor t w₀ w

end Formalism.L2.Pj
