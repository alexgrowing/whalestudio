import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulLawTest

theorem mulA_two {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    mulA A 2 = lift (𝟙 A) (𝟙 A) ≫ μ[A] := by
  simp [mulA, pow_two, Hom.mul_def]

theorem mulA_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] : mulA A 0 = toUnit A ≫ η[A] := by
  simp [mulA, Hom.one_def]

theorem comp_mulA {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (x : T ⟶ A) (n : ℕ) :
    x ≫ mulA A n = x ^ n := by
  simp [mulA, MonObj.comp_pow]

theorem kerPow : KerPowSt :=
  GlobalTheory.AbLaw.FromCube.kerPow GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1

theorem mulPull : MulPullSt :=
  GlobalTheory.AbLaw.FromCube.mulPull GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1

theorem mulN : MulNSt := by
  intro S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ :=
    GlobalTheory.AbLaw.FromCube.mulA_props GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1 S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hd, hm, -⟩ := GlobalTheory.laws_without_cohomology.2.2.1 S _ t P
  have hc := GlobalTheory.abMulN_holds k P'.A P'.g n P'.isAb P'.smoothDim hk
  rw [← hd, ← hc]
  let T : Over (Spec (CommRingCat.of k)) := 𝟙_ _
  have ht : T.hom ≫ t = t := Category.id_comp t
  let φ : (T ⟶ P'.A) →* (Over.mk (T.hom ≫ t) ⟶ P.A) := MonoidHom.mk' (toBase hg.w) (hm T)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y e
      have e' : x.left ≫ g = y.left ≫ g := congrArg CommaMorphism.left e
      ext1
      exact hg.hom_ext e' (by rw [Over.w x, Over.w y])
    · intro y
      refine ⟨Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _), ?_⟩
      ext1
      exact hg.lift_fst _ _ _
  have : Nat.card {x : T ⟶ P'.A // x ^ n = 1} =
      Nat.card {x : Over.mk (T.hom ≫ t) ⟶ P.A // x ^ n = 1} :=
    Nat.card_congr ((MulEquiv.ofBijective φ hφ).toEquiv.subtypeEquiv fun x => by
      change _ ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ hφ.1])
  rw [ht] at this
  exact this.symm

theorem exists_dim_one : ∃ P : PolAV (Spec (CommRingCat.of ℂ)), P.g = 1 := by
  have hΔ : IsUnit (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℂ).Δ := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  obtain ⟨P, -, -, hP, -⟩ := GlobalTheory.WeierstrassCurve.exists_polAV ℂ _ hΔ
  exact ⟨P, hP⟩

def InK {S : Scheme.{0}} (P : PolAV S) (N : ℕ) {T : Over S} (x : T ⟶ P.A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen

theorem separates : ∃ (P : PolAV (Spec (CommRingCat.of ℂ)))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A), InK P 2 x ∧ ¬ InK P 1 x ∧ ¬ InK P 3 x := by
  obtain ⟨P, hP⟩ := exists_dim_one
  have hc := (mulN _ P 2 (by norm_num)).2.2.2.2 ℂ (𝟙 _) (by norm_num)
  rw [hP] at hc
  have hf : Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hn : Nontrivial {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1} :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  obtain ⟨⟨x, hx⟩, hne⟩ := exists_ne (⟨1, one_pow 2⟩ :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A // x ^ 2 = 1})
  have hx1 : x ≠ 1 := fun e => hne (Subtype.ext e)
  refine ⟨P, x, (kerPow _ P 2 (by norm_num) _ x).2 hx, fun h1 => hx1 ?_, fun h3 => hx1 ?_⟩
  · simpa using (kerPow _ P 1 le_rfl _ x).1 h1
  · have := (kerPow _ P 3 (by norm_num) _ x).1 h3
    rwa [pow_succ, hx, _root_.one_mul] at this

theorem mulA_two_ne_id : ∃ P : PolAV (Spec (CommRingCat.of ℂ)), mulA P.A 2 ≠ 𝟙 P.A := by
  obtain ⟨P, x, h2, h1, -⟩ := separates
  refine ⟨P, fun e => h1 ((kerPow _ P 1 le_rfl _ x).2 ?_)⟩
  have hx := (kerPow _ P 2 (by norm_num) _ x).1 h2
  rw [← comp_mulA, e, Category.comp_id] at hx
  simpa using hx

theorem summary : KerPowSt ∧ MulPullSt ∧ MulNSt ∧
    (∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (x : Over.mk (𝟙 (Spec (CommRingCat.of ℂ))) ⟶ P.A),
      InK P 2 x ∧ ¬ InK P 1 x ∧ ¬ InK P 3 x) ∧
    ∃ P : PolAV (Spec (CommRingCat.of ℂ)), mulA P.A 2 ≠ 𝟙 P.A :=
  ⟨kerPow, mulPull, mulN, separates, mulA_two_ne_id⟩

end GlobalTheory.MulLawTest
