import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isPullback_lift_toUnit_fst_left {S : Scheme.{0}} (A B : Over S) (x : 𝟙_ (Over S) ⟶ A) :
    IsPullback (lift (toUnit B ≫ x) (𝟙 B)).left B.hom (fst A B).left (x.left : S ⟶ A.left) := by
  have h1 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (fst A B).left = B.hom ≫ (x.left : S ⟶ A.left) := by
    rw [← Over.comp_left, lift_fst, Over.comp_left]
    rfl
  have h2 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (snd A B).left = 𝟙 B.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h3 : (x.left : S ⟶ A.left) ≫ A.hom = 𝟙 S := Over.w x
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine IsPullback.of_right ?_ h1 hp
  rw [h2, h3]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem triv_of_triv_on_dense_fibres_prod_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG k _ _ A B _ _ N M hA hB hM hamp hN _ hd h0
  have : IsReduced A.left :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k A.left A.hom hA.smooth).1
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG (Sp k) B M hB hM hamp A.left (A ⊗ B).left A.hom (snd A B).left (fst A B).left N hp hN
    (hd.mono ?_) (lift (𝟙 A) (1 : A ⟶ B)).left ?_ h0
  · intro p hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    exact ⟨k, inferInstance, x.left, B.left, _, B.hom, hpx, isPullback_lift_toUnit_fst_left A B x, hx⟩
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory
