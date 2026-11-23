import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AlgClosedHomDescent

theorem hom_descends : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  intro K Ω _ _ _ _ j A A' _ _ B B' _ _ b b' hA hA' hB hB' f hf
  let Ωb := AlgebraicClosure Ω
  let io : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (io.comp j).toAlgebra
  have hJ : spMap io ≫ spMap j = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let P := (Over.pullback (spMap (algebraMap K Ωb))).obj A
  let P' := (Over.pullback (spMap (algebraMap K Ωb))).obj A'
  have hP : IsGrpPullback P A (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A _
  have hP' : IsGrpPullback P' A' (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A' _

  let u : P.left ⟶ B.left := hB.1.lift (pullback.fst A.hom _) (pullback.snd A.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  let u' : P'.left ⟶ B'.left := hB'.1.lift (pullback.fst A'.hom _) (pullback.snd A'.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  have hu₁ : u ≫ b = pullback.fst A.hom _ := hB.1.lift_fst _ _ _
  have hu₂ : u ≫ B.hom = P.hom ≫ spMap io := hB.1.lift_snd _ _ _
  have hu₁' : u' ≫ b' = pullback.fst A'.hom _ := hB'.1.lift_fst _ _ _
  have hu₂' : u' ≫ B'.hom = P'.hom ≫ spMap io := hB'.1.lift_snd _ _ _
  have hPB : IsGrpPullback P B (spMap io) u :=
    hB.cancel (hP.congr hJ.symm hu₁.symm) hu₂
  have hPB' : IsGrpPullback P' B' (spMap io) u' :=
    hB'.cancel (hP'.congr hJ.symm hu₁'.symm) hu₂'

  let fb : P ⟶ P' := Over.homMk (pullback.lift (u ≫ f.left ≫ b') (pullback.snd A.hom _) (by
      rw [Category.assoc, Category.assoc, hB'.1.w, ← Category.assoc f.left, Over.w f, ← Category.assoc, hu₂,
        Category.assoc, hJ]; rfl))
    (pullback.lift_snd _ _ _)
  have hfb₁ : fb.left ≫ pullback.fst A'.hom _ = u ≫ f.left ≫ b' := pullback.lift_fst _ _ _
  have hfb₂ : fb.left ≫ P'.hom = P.hom := Over.w fb
  have hfbu : u ≫ f.left = fb.left ≫ u' := by
    apply hB'.1.hom_ext
    · rw [Category.assoc, Category.assoc, hu₁', hfb₁]
    · rw [Category.assoc, Over.w f, hu₂, Category.assoc, hu₂', ← Category.assoc, hfb₂]
  have hfbm : IsMonHom fb :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).2 B B' P P' u u' f fb hPB hPB' hfbu).2 hf

  obtain ⟨g, hg, hge⟩ := GlobalTheory.T.exists_mon_hom_over_algebraic_closure K Ωb A A' hA hA' fb hfbm
  let L := algebraicClosure K Ωb
  have hbij : Function.Bijective (algebraMap K L) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap K L)) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsIso (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  let q := pullback.fst A.hom (spMap (algebraMap K L))
  let q' := pullback.fst A'.hom (spMap (algebraMap K L))

  let f₀ : A ⟶ A' := Over.homMk (inv q ≫ g.left ≫ q') (by
    have hg' : g.left ≫ pullback.snd A'.hom (spMap (algebraMap K L)) = pullback.snd A.hom _ := Over.w g
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g.left, hg', ← pullback.condition,
      IsIso.inv_hom_id_assoc])
  have hq : q ≫ f₀.left = g.left ≫ q' := by
    show q ≫ inv q ≫ g.left ≫ q' = _
    rw [IsIso.hom_inv_id_assoc]
  have hf₀ : IsMonHom f₀ :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K L (algebraMap K L)).2 A A' _ _ q q' f₀ g
      (isGrpPullback_pullback A _) (isGrpPullback_pullback A' _) hq).1 hg
  refine ⟨f₀, hf₀, ?_⟩
  have hepi : Epi u := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).1 B.left P.left B.hom P.hom u hPB.1).1
  rw [← cancel_epi u, ← Category.assoc, hu₁, ← GlobalTheory.Spread.bcMap_fst A.hom L.val, Category.assoc, hq, hge, hfb₁]

end GlobalTheory.AlgClosedHomDescent
