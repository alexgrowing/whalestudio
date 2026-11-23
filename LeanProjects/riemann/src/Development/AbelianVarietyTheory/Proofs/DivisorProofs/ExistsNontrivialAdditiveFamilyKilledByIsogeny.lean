import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedLineBundleEquivariantGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTrivialPullbackOfIsPullbackGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterEqOneOfDescendedLineBundleTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGeneratoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nontriv_family : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite N.hom → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → i ≠ 1 → ∃ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB ∧ IsAdditive M ∧ Triv (ev M (fst A T ≫ q) (snd A T)) ∧ ¬ Triv M := by
  intro K _ _ A A' N _ _ _ i q hA hA' hi hq hNf hqf hqfl hqs hker hi1
  have hmono : Mono i := hker.mono_fst_of_mono
  have hcomm : IsCommMonObj A := hA.comm
  have : IsCommMonObj N := AbelianSubgroupFinite.isCommMonObj_of_mono i
  have hN1 : 𝟙 N ≠ (1 : N ⟶ N) := by
    intro h
    apply hi1
    rw [← Category.id_comp i, h, MonObj.one_comp]
  obtain ⟨T, χ, hχ, hne⟩ := GlobalTheory.T.exists_nontrivial_character_finite_comm_group K N hNf hN1
  obtain ⟨M, e, hM, he⟩ := GlobalTheory.T.exists_descended_lineBundle_equivariantGenerator _ A A' N T i q χ hi hq hqf hqfl hqs hker hχ
  exact ⟨T, M, hM, GlobalTheory.T.characterLineBundle_additive_of_equivariantGenerator K A A' N T i q χ M e hA hA' hi hq hqf hqfl hqs hker hχ hM he,
    GlobalTheory.T.cechTrivial_pullback_of_isPullbackGenerator _ _ _ M e he.1, fun h => hne (GlobalTheory.T.character_eq_one_of_descended_lineBundle_trivial K A A' N T i q χ M e hA hq hker hM he h)⟩

end GlobalTheory.CharKer
