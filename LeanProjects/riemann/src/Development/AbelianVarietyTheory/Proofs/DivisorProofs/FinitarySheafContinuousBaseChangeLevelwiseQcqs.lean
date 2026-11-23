import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_bc_sch_qcqs (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (S X : Scheme.{0})
    (r : X ⟶ S) (hqc : QuasiCompact r) (hqs : QuasiSeparated r) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G : I ⥤ Over S) (c : Cone G) (hc : IsLimit c) (hG : ∀ i, IsAffine (G.obj i).left) :
    ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨e, -⟩ := GlobalTheory.EtC.bc_sch_iso S X r
  let H : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget X
  have hl : IsLimit (H.mapCone c) := isLimitOfPreserves H hc
  have hcomp : ∀ i, CompactSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiCompact (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqc
    have hc' := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (G.obj i).hom r)
    exact hc'
  have hqsp : ∀ i, QuasiSeparatedSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiSeparated (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqs
    have hs' := quasiSeparatedSpace_of_quasiSeparated (pullback.fst (G.obj i).hom r)
    exact hs'
  have haff : ∀ (i j : I) (f : i ⟶ j), IsAffineHom ((G ⋙ H).map f) := by
    intro i j f
    haveI := hG i
    haveI := hG j
    have hsq : IsPullback ((G ⋙ H).map f) (pullback.fst (G.obj i).hom r) (pullback.fst (G.obj j).hom r)
        (G.map f).left := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (G.obj j).hom r) (h₂₂ := (G.obj j).hom) (v₁₃ := r) ?_ ?_ ?_
      · have e1 : (G ⋙ H).map f ≫ pullback.snd (G.obj j).hom r = pullback.snd (G.obj i).hom r := by
          exact pullback.lift_snd _ _ _
        have e2 : (G.map f).left ≫ (G.obj j).hom = (G.obj i).hom := Over.w (G.map f)
        have key : ∀ {P₁ P₂ P₃ P₄ : Scheme.{0}} {l : P₁ ⟶ P₃} {rr : P₂ ⟶ P₄} {a a' : P₁ ⟶ P₂} {b b' : P₃ ⟶ P₄},
            a = a' → b = b' → IsPullback a' l rr b' → IsPullback a l rr b := by
          rintro _ _ _ _ _ _ _ _ _ _ rfl rfl h; exact h
        exact key e1 e2 (IsPullback.of_hasPullback (G.obj i).hom r).flip
      · exact pullback.lift_fst _ _ _
      · exact (IsPullback.of_hasPullback (G.obj j).hom r).flip
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip (isAffineHom_of_isAffine _)
  have h1 : ContCone R F (sch.mapCone (H.mapCone c)) :=
    GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions R F hF I (G ⋙ H) (H.mapCone c) hl hcomp hqsp haff
  have hb := GlobalTheory.EtC.eqv_basic R F
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ H ⋙ sch) (G ⋙ bc (sch.map r)) (sch.mapCone (H.mapCone c))
    ((bc (sch.map r)).mapCone c) (Functor.whiskerLeft G e.hom) (e.hom.app c.pt) ?_ ?_ ?_).1 h1
  · intro i
    exact e.hom.naturality (c.π.app i)
  · intro i
    exact hb.1 _ _ _ inferInstance
  · exact hb.1 _ _ _ inferInstance

theorem contCone_bc_qcqsOver : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S), QcqsOver p → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((bc p).mapCone c)) := by
  intro R _ F hF S E p hp I _ _ G c hc hG
  refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S E p I G c ?_
  intro k
  obtain ⟨X, r, e, hqc, hqs, he⟩ := hp k
  exact ⟨X, r, e, he, contCone_bc_sch_qcqs R F hF S X r hqc hqs I G c hc hG⟩

end GlobalTheory.EtC
