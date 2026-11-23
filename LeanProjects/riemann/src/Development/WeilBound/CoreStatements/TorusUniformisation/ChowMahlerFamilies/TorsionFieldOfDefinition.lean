import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TorsionFieldOfDefinition

theorem exists_field_alg (C : Type) [CommRing C] [Algebra ℚ C] [Module.Finite ℚ C] :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ ∀ (ψ : C →+* ℂ) (c : C), ψ c ∈ F := by
  classical
  have hint : ∀ c : C, IsIntegral ℚ c := fun c => Algebra.IsIntegral.isIntegral c
  let bs := Module.finBasis ℚ C
  let S : Finset ℂ := Finset.univ.biUnion (fun i => ((minpoly ℚ (bs i)).aroots ℂ).toFinset)
  have hroot : ∀ (ψ : C →+* ℂ) i, ψ (bs i) ∈ S := by
    intro ψ i
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset]
    refine ⟨i, Polynomial.mem_aroots.mpr ⟨minpoly.ne_zero (hint _), ?_⟩⟩
    have h := Polynomial.aeval_algHom_apply ψ.toRatAlgHom (bs i) (minpoly ℚ (bs i))
    rw [minpoly.aeval, map_zero] at h
    exact h
  refine ⟨IntermediateField.adjoin ℚ (S : Set ℂ), ?_, ?_⟩
  · apply IntermediateField.finiteDimensional_adjoin
    intro z hz
    have hz' : z ∈ S := hz
    simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Multiset.mem_toFinset] at hz'
    obtain ⟨i, hzi⟩ := hz'
    obtain ⟨-, hz0⟩ := Polynomial.mem_aroots.mp hzi
    exact ⟨minpoly ℚ (bs i), minpoly.monic (hint _), by rwa [← Polynomial.aeval_def]⟩
  · intro ψ c
    rw [← bs.sum_repr c, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin ℚ _ (hroot ψ i))

theorem exists_field_ring (L : Type) [Field L] [NumberField L] (B : Type) [CommRing B]
    (φ : L →+* B) (hφ : φ.Finite) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ (∀ (σ : L →+* ℂ) (c : L), σ c ∈ F) ∧
      ∀ (ψ : B →+* ℂ) (c : B), ψ c ∈ F := by
  letI : Algebra L B := φ.toAlgebra
  letI : Algebra ℚ B := (φ.comp (algebraMap ℚ L)).toAlgebra
  haveI : IsScalarTower ℚ L B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite L B := hφ
  haveI : Module.Finite ℚ B := Module.Finite.trans L B
  obtain ⟨F₁, hF₁, h₁⟩ := exists_field_alg L
  obtain ⟨F₂, hF₂, h₂⟩ := exists_field_alg B
  haveI := hF₁
  haveI := hF₂
  exact ⟨F₁ ⊔ F₂, inferInstance, fun σ c => le_sup_left (a := F₁) (h₁ σ c),
    fun ψ c => le_sup_right (a := F₁) (h₂ ψ c)⟩

theorem exists_field_scheme (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (W : Scheme.{0})
    (p : W ⟶ Sp L) [IsFinite p] :
    ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F),
      (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ w : Sp ℂ ⟶ W, w ≫ p = spMap σ →
        ∃ y : Sp F ⟶ W, y ≫ p = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = w := by
  haveI : IsAffine W := isAffine_of_isAffineHom p
  obtain ⟨q, hq⟩ : ∃ q : CommRingCat.of L ⟶ Γ(W, ⊤), Spec.map q = W.isoSpec.inv ≫ p :=
    ⟨_, Spec.map_preimage _⟩
  have hfin : q.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hq]
    infer_instance
  obtain ⟨F, hF, hσF, hψF⟩ := exists_field_ring L Γ(W, ⊤) q.hom hfin
  refine ⟨F, hF, σ.codRestrict F (hσF σ), fun x => rfl, fun w hw => ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(W, ⊤) ⟶ CommRingCat.of ℂ, Spec.map g = w ≫ W.isoSpec.hom :=
    ⟨_, Spec.map_preimage _⟩
  let gF : Γ(W, ⊤) →+* F := g.hom.codRestrict F (hψF g.hom)
  refine ⟨Spec.map (CommRingCat.ofHom gF) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have hqg : q ≫ g = CommRingCat.ofHom σ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, hq]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact hw
    dsimp only [spMap]
    rw [Category.assoc, ← hq, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg (fun f : CommRingCat.of L ⟶ CommRingCat.of ℂ => f.hom x) hqg
  · dsimp only [spMap]
    rw [← Category.assoc, ← Spec.map_comp]
    have hc : CommRingCat.ofHom gF ≫ CommRingCat.ofHom (algebraMap F ℂ) = g := by
      ext x
      rfl
    rw [hc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PositivityTheory.Xgn.TorsionFieldOfDefinition

private theorem comp_mulN_lemma {S : Scheme} {G : Over S} [GrpObj G] {X : Over S} (x : X ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, Hom.one_def]
    show x ≫ (toUnit G ≫ η) = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | succ k ih =>
    rw [pow_succ, Hom.mul_def, ← ih]
    show x ≫ (CartesianMonoidalCategory.lift (mulN G k) (𝟙 G) ≫ μ) = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id]

theorem PositivityTheory.Xgn.torsion_field_of_definition : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left := by
  intro L _ _ σ P n hn
  haveI := P.isAb.comm
  haveI := P.isAb.smooth
  haveI := P.isAb.proper
  have hu : IsUnit ((n : ℕ) : Γ(Sp L, ⊤)) := by
    have h0 : IsUnit ((n : ℕ) : L) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
    have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    rwa [map_natCast] at h1
  haveI hfin : IsFinite (torsion P.A n).hom := GlobalTheory.GrpTangent.isFinite_torsion P.A hu
  obtain ⟨F, hF, e, he, hlift⟩ :=
    PositivityTheory.Xgn.TorsionFieldOfDefinition.exists_field_scheme L σ (torsion P.A n).left (torsion P.A n).hom
  refine ⟨F, hF, e, he, fun x hx => ?_⟩
  have hx' : x ≫ mulN P.A n = (toUnit _ ≫ η : Over.mk (spMap σ) ⟶ P.A) := by
    rw [comp_mulN_lemma, hx, Hom.one_def]
  let t : Over.mk (spMap σ) ⟶ torsion P.A n := pullback.lift x (toUnit _) hx'
  obtain ⟨y, hy1, hy2⟩ := hlift t.left (Over.w t)
  refine ⟨y ≫ (torsion.ι P.A n).left, ?_, ?_⟩
  · rw [Category.assoc, Over.w (torsion.ι P.A n), hy1]
  · rw [← Category.assoc, hy2, ← Over.comp_left]
    congr 1
    exact pullback.lift_fst _ _ _
