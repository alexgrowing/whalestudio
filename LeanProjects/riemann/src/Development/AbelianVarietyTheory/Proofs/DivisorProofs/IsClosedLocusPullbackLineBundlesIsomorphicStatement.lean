import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedLocusPullbackLineBundlesIsomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesawStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_locus_pullback_lineBundles_isomorphic : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (Z₁ : Scheme.{0}) [IsLocallyNoetherian Z₁] (t₁ : Z₁ ⟶ Sp Rg) (A₁ B₁ : Over Z₁) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → RelAmple A L → IsGrpPullback A₁ A t₁ φA₁ → IsGrpPullback B₁ B t₁ φB₁ → IsMonHom Φ₁ → ∃ (Z : Scheme.{0}) (i : Z ⟶ Z₁), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (u : T ⟶ Z₁) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (ψA : A'.left ⟶ A₁.left) (ψB : B'.left ⟶ B₁.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A₁ u ψA → IsGrpPullback B' B₁ u ψB → Φ'.left ≫ ψB = ψA ≫ Φ₁.left → (LBIso (L.pull (ψA ≫ φA₁)) ((M.pull (ψB ≫ φB₁)).pull Φ'.left) ↔ ∃ w : T ⟶ Z, w ≫ i = u) := by
  first | (exact @GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (exact GlobalTheory.HomFixTrivLocus.isoLocus_closed) | (intros; apply GlobalTheory.HomFixTrivLocus.isoLocus_closed  <;> assumption)
