import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.RelCotAb

theorem ev_divMap_pairPt_periodChart : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex →
    ∀ v ∈ c.e.target, ∀ (z u : Fin g → ℂ) (hz : (ex (v, z)).1 ≫ A.hom = (ex (v, z + u)).1 ≫ A.hom)
      (W₁ : A.left.Opens) (h : Γ(A.left, W₁)),
      ev _ σ (GlobalTheory.RelCotAb.divMap A ⁻¹ᵁ W₁) ((GlobalTheory.RelCotAb.divMap A).app W₁ h)
          (GlobalTheory.RelCotAb.pairPt A (ex (v, z)) (ex (v, z + u)) hz) =
        ev (A.hom ≫ p) σ W₁ h (ex (v, u)) := by
  intro k _ S p D A _ _ g w σ c τ ex H v hv z u hz W₁ h
  obtain ⟨h₁, h₂, -⟩ := H.2.2 v hv
  have hπ : divMap A ≫ A.hom ≫ p = Limits.pullback.fst A.hom A.hom ≫ A.hom ≫ p := by
    rw [Category.assoc, ← Limits.pullback.condition_assoc, ← Category.assoc]
    exact congrArg (· ≫ A.hom ≫ p) (shear_left_fst A)
  let e (z : Fin g → ℂ) : Over.mk (c.e.symm v).1 ⟶ A := Over.homMk (ex (v, z)).1 (h₁ z)
  have hm : e z * e u = e (z + u) := Over.OverMorphism.ext (h₂ z u _ _ rfl rfl)
  have hp : GlobalTheory.Points.PtsOver.map (divMap A) hπ _ (pairPt A (ex (v, z)) (ex (v, z + u)) hz) = ex (v, u) :=
    Subtype.ext (lift_divMap A (e z) (e (z + u)) (e u) hm)
  rw [← hp]
  exact ev_app _ hπ _ _ _

end GlobalTheory.RelCotAb
