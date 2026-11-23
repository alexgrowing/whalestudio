import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem scalar_pullback_spec_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (x y : A) :
    scal p (x * y) = scal p x * scal p y := by
  unfold scal; rw [map_mul, map_mul]

theorem Trait.exp_mul_left : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  intro R _ _ _ D C W _ _ _ T k s F a b c ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩
  refine ⟨DVR.SecOps.secScale (scal T.G.hom c) σ, ⟨σ', f', ?_, hP, hE⟩, ?_⟩
  · intro Z r z J J' hJ hJ'
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hC Z r z J J' hJ hJ', scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring
  · intro Z p p' hp z J hJ
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hs Z p p' hp z J hJ, scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring

end GlobalTheory.Mum
