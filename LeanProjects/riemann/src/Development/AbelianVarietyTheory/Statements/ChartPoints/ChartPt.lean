import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChTor

def ChartPt (p : ℕ) {O : Type} [CommRing O] {d : ℕ} {G : Over (Sp O)}
    (x : ∀ m : ℕ, algOver O (JetR O (Fin 1 × Fin d) m) ⟶ G) (c : Fin d → O) (P : algOver O O ⟶ G) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (ψ : JetR O (Fin 1 × Fin d) k →ₐ[O] O ⧸ Ideal.span {((p : O) ^ n)}),
    (∀ i, ψ (zR k ((0 : Fin 1), i)) = Ideal.Quotient.mk _ (c i)) ∧
    algOverHom (Ideal.Quotient.mkₐ O (Ideal.span {((p : O) ^ n)})) ≫ P = algOverHom ψ ≫ x k

abbrev Pts {C : Type} [Field C] (A : Over (Sp C)) : Type := (Over.mk (𝟙 (Sp C)) : Over (Sp C)) ⟶ A

def IsTate (p : ℕ) {C : Type} [Field C] {A : Over (Sp C)} [GrpObj A] (s : ℕ → Pts A) : Prop :=
  ∀ m, s m ^ (p ^ m) = 1 ∧ s (m + 1) ^ p = s m

def FHAll (p : ℕ) (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {d : ℕ} (F : Fin d → PS O 2 d) : Prop :=
  ∀ m : ℕ, Module.Free O (QF F (p ^ m)) ∧ Module.Finite O (QF F (p ^ m)) ∧ IsReduced (C ⊗[O] QF F (p ^ m)) ∧
    ∀ q : QF F (p ^ m), (∀ φ : QF F (p ^ m) →ₐ[O] O, φ q = 0) → q = 0

def IsUs (p : ℕ) {C : Type} [Field C] {O : Type} [CommRing O] [Algebra O C] {d : ℕ} {G : Over (Sp O)}
    (F : Fin d → PS O 2 d) (x : ∀ m : ℕ, algOver O (JetR O (Fin 1 × Fin d) m) ⟶ G) (A : Out.PolAV (Sp C))
    (gen : A.A.left ⟶ G.left) (s : ℕ → Pts A.A) (u : PS O 1 d) : Prop :=
  IsCh F u ∧ ∀ (m : ℕ) (φ : QF F (p ^ m) →ₐ[O] O) (P : algOver O O ⟶ G) (z : Pts A.A),
    ChartPt p x (fun i => φ (Ideal.Quotient.mk _ (MvPowerSeries.X ((0 : Fin 1), i)))) P →
    z.left ≫ gen = spMap (algebraMap O C) ≫ P.left →
    ∃ w : Cˣ, (w : C) = algebraMap O C (φ (Ideal.Quotient.mk _ u)) ∧
      Out.WeilIs A.A A.L ((p ^ m : ℕ) : ℤ) z (s m) (unitOn w)

def ChTorSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsSeparated G.hom →
    ∀ (A : Out.PolAV (Sp C)) (gen : A.A.left ⟶ G.left), IsGrpPullback A.A G (spMap (algebraMap O C)) gen →
    ∀ (d : ℕ) (F : FGLaw O d) (x : ∀ m : ℕ, algOver O (JetR O (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
      FHAll p C F.F →
      (∀ s, IsTate p s → ∃! u, IsUs p F.F x A gen s u) ∧
      (∀ s s' u u', IsTate p s → IsTate p s' → IsUs p F.F x A gen s u → IsUs p F.F x A gen s' u' →
        IsUs p F.F x A gen (fun m => s m * s' m) (u * u')) ∧
      ∀ u, IsCh F.F u → ∃ s, IsTate p s ∧ IsUs p F.F x A gen s u

end GlobalTheory.ChTor
