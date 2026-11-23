import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

set_option autoImplicit false
noncomputable section
open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def mulF {O : Type} [CommRing O] {d : ℕ} (F : Fin d → PS O 2 d) : ℕ → Pt O 1 d
  | 0 => 0
  | n + 1 => addOf F (mulF F n) (pt O d 0)

abbrev QF {O : Type} [CommRing O] {d : ℕ} (F : Fin d → PS O 2 d) (p : ℕ) : Type :=
  PS O 1 d ⧸ Ideal.span (Set.range (mulF F p))

section Forms

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

def FHSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
      (_ : Out.UnifPre (maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (iota : T →+* O), IsLocalHom iota →
      ∀ m : ℕ, Module.Free O (QF (F.mapF iota) (p ^ m)) ∧ Module.Finite O (QF (F.mapF iota) (p ^ m)) ∧
        IsReduced (C ⊗[O] QF (F.mapF iota) (p ^ m)) ∧
        ∀ q : QF (F.mapF iota) (p ^ m), (∀ φ : QF (F.mapF iota) (p ^ m) →ₐ[O] O, φ q = 0) → q = 0

end Forms

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
