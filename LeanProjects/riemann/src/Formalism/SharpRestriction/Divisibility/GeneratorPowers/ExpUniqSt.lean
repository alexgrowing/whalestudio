import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPolynomial (X)

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {S : Type} [CommRing S]

def IsExpHomR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  (∀ m, homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) ∧
  ∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d =>
      (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin d) S)) ≫ x m =
    (homAt x0 (jetCopy d m (0 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m) *
      (homAt x0 (jetCopy d m (1 : Fin 2) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) ≫ x m)

def SameTanR (x0 : Sp S ⟶ Xo.X) (d : ℕ) (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G) : Prop :=
  ∀ j : Fin d,
    homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1 =
      homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x' 1

end

def ExpUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (d : ℕ) (x x' : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G),
    IsExpHomR y.x d x → IsExpHomR y.x d x' → SameTanR y.x d x x' → x = x'

def ExpUniqRawSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'

def ExpUniqLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (S : Type) [CommRing S] [IsLocalRing S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X) (d : ℕ)
    (x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G),
    IsExpHomR x0 d x → IsExpHomR x0 d x' → SameTanR x0 d x x' → x = x'

end Formalism.MainNotions.ModuliIntegralCharts.H1
