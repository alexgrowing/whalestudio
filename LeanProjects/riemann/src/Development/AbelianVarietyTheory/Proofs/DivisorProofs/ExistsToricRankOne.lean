import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure PreCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) where

  S : Scheme.{0}

  π : S ⟶ Sp R
  proper : IsProper π

  gp : Sp (FractionRing R) ⟶ S
  gp_π : gp ≫ π = jK R

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)

  n : ℕ
  n_prime : n.Prime
  n_odd : Odd n
  n_unit : IsUnit (n : R)

  lab : ∀ j : ℕ, QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j) →
    (TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G')
      (hD : IsPullDeg (io.comp φ) D.toPre D'.toPre),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W') F] [Algebra (FractionRing R) F]
        (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
        (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W') F (algebraMap W' _ (io (φ r)))) →
        ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (n ^ j)) (p₁ : QkPt D.toPre F (n ^ j))
          (p' : QkPt D'.toPre F (n ^ j)) (x' : TFK (R := W') F ⟶ A'.A),
          QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF (io.comp φ) hD F p₁.g p'.g →
          x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK W') ≫ β = spMap em.toRingHom ≫ (lab j p).left ≫ α →
          QkToAkU U'.toUnifPre F (n ^ j) p' x'

attribute [instance] PreCover.grp PreCover.comm

def LabCover.toPreCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    (C : LabCover D) : PreCover D where
  S := C.S
  π := C.π
  proper := C.proper
  gp := C.gp
  gp_π := C.gp_π
  G := C.G
  semi := C.semi
  P := C.P
  A := C.A
  α := C.α
  α_cart := C.α_cart
  α_lb := C.α_lb
  n := C.n
  n_prime := C.n_prime
  n_odd := C.n_odd
  n_unit := C.n_unit
  lab := C.lab
  trait := C.trait

theorem PreCover.exists_toric_rank_one : ∃ D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)),
    Module.finrank ℤ D.toPre.X = 1 ∧ Has D ∧ ∃ C : PreCover D, C.n = 3 := by
  obtain ⟨D, h1, h2, -, C, hC⟩ := LabCover.exists_toric_rank_one
  exact ⟨D, h1, h2, C.toPreCover, hC⟩

end GlobalTheory.Mum
