import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HomFinExt

open GlobalTheory.Spread GlobalTheory.HomExtNormal

theorem exists_finite_hom : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap ga)).obj A ⟶ (Over.pullback (spMap ga)).obj A', IsMonHom f → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (f' : (Over.pullback (spMap io)).obj A ⟶ (Over.pullback (spMap io)).obj A'), io.Finite ∧ l.comp io = j.comp ga ∧ IsMonHom f' ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A.hom (spMap ga)) (p' : Z ⟶ pullback A.hom (spMap io)) (t : Z ⟶ Sp Ω'), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.left ≫ pullback.fst _ _ = p' ≫ f'.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ ga A A' _ _ hA hA' f hf
  haveI := hf
  have := hA.proper
  have := hA'.proper
  have := hA.smooth
  have := hA'.smooth
  let Ωb := AlgebraicClosure Ω
  let j : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (j.comp ga).toAlgebra
  let Kb := algebraicClosure K Ωb
  have hcomp : spMap j ≫ spMap ga = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨f₁, hf₁, e₁⟩ := exists_pull_hom (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp f
  obtain ⟨g, hg, eg⟩ := GlobalTheory.T.exists_mon_hom_over_algebraic_closure K Ωb A A' hA hA' f₁ hf₁
  obtain ⟨s, hs⟩ := GlobalTheory.HomPairDescent.exists_descend (K := K) (Ω := Kb) A A' g
  let L : IntermediateField K Kb := IntermediateField.adjoin K (s : Set Kb)
  obtain ⟨g', hg'⟩ := hs L (IntermediateField.subset_adjoin _ _)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A L.val
  have gB := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A' L.val
  obtain ⟨-, hmon⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff L Kb L.val.toRingHom
  have hg'm : IsMonHom g' := (hmon _ _ _ _ _ _ g' g gA gB hg').1 hg
  let l : L →+* Ωb := Kb.val.toRingHom.comp L.val.toRingHom
  refine ⟨L, inferInstance, algebraMap K L, Ωb, inferInstance, j, l, g', RingHom.finite_algebraMap.mpr hfin,
    ?_, hg'm, ?_⟩
  · ext x
    change Kb.val (L.val (algebraMap K L x)) = algebraMap K Ωb x
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro Z p p' t h1 h2 h3
    have hP : (p ≫ pullback.fst _ _) ≫ A.hom = t ≫ spMap (algebraMap K Ωb) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h2, Category.assoc, hcomp]
    let P : Z ⟶ pullback A.hom (spMap (algebraMap K Ωb)) := pullback.lift (p ≫ pullback.fst _ _) t hP
    have hPp : P ≫ pullMap (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp A = p := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, pullback.lift_fst]
      · rw [Category.assoc, pullMap_snd, pullback.lift_snd_assoc, h2]
    have hQ : (P ≫ bcMap A.hom Kb.val) ≫ bcMap A.hom L.val = p' := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, bcMap_fst, pullback.lift_fst, h1]
      · rw [Category.assoc, bcMap_snd, Category.assoc, bcMap_snd_assoc, pullback.lift_snd_assoc, h3]
        rw [← Spec.map_comp]; rfl
    calc p ≫ f.left ≫ pullback.fst _ _
        = P ≫ f₁.left ≫ pullback.fst _ _ := by rw [e₁, ← hPp, Category.assoc]
      _ = P ≫ bcMap A.hom Kb.val ≫ g.left ≫ pullback.fst _ _ := by rw [eg]
      _ = p' ≫ g'.left ≫ pullback.fst _ _ := by
        rw [← hQ, Category.assoc, Category.assoc, ← Category.assoc (bcMap A.hom L.val), hg', Category.assoc,
          bcMap_fst]

end GlobalTheory.HomFinExt
