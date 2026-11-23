import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqIdOfFixesTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppTopSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBuStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SeesawGlobal

theorem isPullback_tensor {S : Scheme.{0}} (T A : Over S) :
    IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
  (IsPullback.of_hasPullback T.hom A.hom).flip

theorem exists_closed_triv :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (T : Over (Sp K)) (N : LB (T ⊗ P.A).left), N.IsLB → (∃ t : (N.pull (lift (𝟙 T) (1 : T ⟶ P.A)).left).Gen, t.IsGen) → ∃ (Z : Scheme.{0}) (i : Z ⟶ T.left), IsClosedImmersion i ∧ ∀ (T' : Over (Sp K)) (h : T' ⟶ T), (∃ t : (N.pull (h ▷ P.A).left).Gen, t.IsGen) ↔ ∃ u : T'.left ⟶ Z, u ≫ i = h.left := by
  intro hL _ K _ _ P T N hN h0
  have hproj : GlobalTheory.AbLaw.IsProjBy P.A.hom := by
    obtain ⟨n, -, m, s, h₁, h₂⟩ := GlobalTheory.AbLaw.polAV_veryAmpleBy hL.polBaseChange (Sp K) P K (𝟙 _) P.A.left
      (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
    exact ⟨_, h₁, m, s, h₂⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hL.globalFns K T P.A P.isAb hproj N hN
  refine ⟨H.left, j.left, hj, fun T' h => ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, hy⟩ := (hH T' h).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
    exact ⟨y.left, congrArg (·.left) hy⟩
  · rintro ⟨u, hu⟩
    have hw : u ≫ H.hom = T'.hom := by rw [← Over.w j, ← Category.assoc, hu, Over.w h]
    have hloc := (hH T' h).2 ⟨Over.homMk u hw, Over.OverMorphism.ext hu⟩
    refine GlobalTheory.exists_gen_of_local_of_section (T' ⊗ P.A).left T'.left (fst T' P.A).left
      (lift (𝟙 T') (1 : T' ⟶ P.A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 T') (1 : T' ⟶ P.A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ P.A P.isAb _ _ T'.hom _ _ (isPullback_tensor T' P.A))
      hloc ?_
    refine GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _ (GlobalTheory.AbLaw.CubeOpen.triv_comp h.left ?_ h0)
    have e : h ≫ lift (𝟙 T) (1 : T ⟶ P.A) = lift (𝟙 T') (1 : T' ⟶ P.A) ≫ h ▷ P.A := by
      ext <;> simp
    exact congrArg (·.left) e

end GlobalTheory.SeesawGlobal
