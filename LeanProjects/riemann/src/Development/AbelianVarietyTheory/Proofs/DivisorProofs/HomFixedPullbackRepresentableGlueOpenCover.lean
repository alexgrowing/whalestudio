import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem homFixRep_glue_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB J U hU hloc
  refine GlobalTheory.T.homFixedPullback_representable_glue (fun H A B _ _ _ _ L M Φ hΦ hA hB hL hM rA rB h => GlobalTheory.HomFixLocal.lbIso_pull_of_local H A B L M Φ hΦ hA hB hL hM rA rB h) S A B L M hA hB hL hM rA rB J (fun i => (U i).toScheme) (fun i => (U i).ι) (fun i => inferInstance) (fun s => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hU s; exact ⟨i, by simpa [Scheme.Opens.range_ι] using hi⟩
  · obtain ⟨AU, gA, BU, gB, φA, φB, pA, pB, R, h1, h2, h3⟩ := hloc i; exact ⟨AU, BU, gA, gB, φA, φB, R, pA, pB, h1, h2, h3⟩

end GlobalTheory
