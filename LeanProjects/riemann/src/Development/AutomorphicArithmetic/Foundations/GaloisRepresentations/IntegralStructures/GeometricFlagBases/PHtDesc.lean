import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo
open Opposite

noncomputable section

namespace UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits

section Alg
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]

private abbrev FI : Type := {L : IntermediateField k Ω // FiniteDimensional k L}

private theorem dir (a b : FI k Ω) : ∃ c : FI k Ω, a ≤ c ∧ b ≤ c := by
  have := a.2; have := b.2
  exact ⟨⟨a.1 ⊔ b.1, IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩

private instance : IsDirected (FI k Ω) (· ≤ ·) := ⟨dir k Ω⟩

private instance : Nonempty (FI k Ω) := ⟨⟨⊥, inferInstance⟩⟩

private instance : IsFiltered (FI k Ω) := isFiltered_of_directed_le_nonempty _

private def Dg : FI k Ω ⥤ CommRingCat.{0} where
  obj L := .of L.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id L := rfl
  map_comp f g := rfl

private def cg : Cocone (Dg k Ω) where
  pt := .of Ω
  ι := { app := fun L => CommRingCat.ofHom (algebraMap L.1 Ω)
         naturality := fun L L' f => rfl }

private theorem exists_rep [Algebra.IsAlgebraic k Ω] (x : Ω) : ∃ (L : FI k Ω) (y : L.1), algebraMap L.1 Ω y = x :=
  ⟨⟨IntermediateField.adjoin k {x}, IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral x)⟩, ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩, rfl⟩

private def cgColim [Algebra.IsAlgebraic k Ω] : IsColimit (cg k Ω) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i j xi xj h => ?_))
  · obtain ⟨L, y, hy⟩ := exists_rep k Ω (x : Ω)
    exact ⟨L, y, hy.symm⟩
  · obtain ⟨c, hi, hj⟩ := dir k Ω i j
    refine ⟨c, homOfLE hi, homOfLE hj, ?_⟩
    apply Subtype.ext
    exact h

end Alg

section Geo
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

private def tr {L L' : IntermediateField k Ω} (h : L ≤ L') : geom L' p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

private theorem tr_fst {L L' : IntermediateField k Ω} (h : L ≤ L') :
    tr p h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem tr_snd {L L' : IntermediateField k Ω} (h : L ≤ L') :
    tr p h ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) :=
  pullback.lift_snd _ _ _

private theorem pj_fst (L : IntermediateField k Ω) :
    LateralTheory.EWeil.StabPf.proj L p ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem pj_snd (L : IntermediateField k Ω) :
    LateralTheory.EWeil.StabPf.proj L p ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := pullback.lift_snd _ _ _

private theorem pj_tr {L L' : IntermediateField k Ω} (h : L ≤ L') :
    LateralTheory.EWeil.StabPf.proj L' p ≫ tr p h = LateralTheory.EWeil.StabPf.proj L p := by
  apply pullback.hom_ext
  · rw [Category.assoc, tr_fst, pj_fst, pj_fst]
  · rw [Category.assoc, tr_snd, ← Category.assoc, pj_snd, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, pj_snd]
    rfl

variable (k Ω) in

private def Gd : (FI k Ω)ᵒᵖ ⥤ Scheme.{0} where
  obj L := geom L.unop.1 p
  map f := tr p (leOfHom f.unop)
  map_id L := by
    apply pullback.hom_ext
    · exact (tr_fst p _).trans (Category.id_comp _).symm
    · refine (tr_snd p _).trans ?_
      refine Eq.trans ?_ (Category.id_comp _).symm
      have e : CommRingCat.ofHom (IntermediateField.inclusion (le_refl L.unop.1)).toRingHom = 𝟙 _ := rfl
      exact (congrArg (fun t => pullback.snd _ _ ≫ Spec.map t) e).trans (by simp)
  map_comp {L L' L''} f g := by
    apply pullback.hom_ext
    · refine (tr_fst p _).trans ?_
      rw [Category.assoc, tr_fst, tr_fst]
    · refine (tr_snd p _).trans ?_
      rw [Category.assoc, tr_snd, ← Category.assoc, tr_snd, Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rfl

variable (k Ω) in

private def cn : Cone (Gd k Ω p) where
  pt := geom Ω p
  π := { app := fun L => LateralTheory.EWeil.StabPf.proj L.unop.1 p
         naturality := fun L L' f => (Category.id_comp _).trans (pj_tr p (leOfHom f.unop)).symm }

private def bt : FI k Ω := ⟨⊥, inferInstance⟩

section Lim
variable {T : Scheme.{0}} (a : ∀ L : FI k Ω, T ⟶ geom L.1 p)
  (ha : ∀ (L L' : FI k Ω) (h : L.1 ≤ L'.1), a L' ≫ tr p h = a L)

include ha in
private theorem a_snd (L L' : FI k Ω) (h : L.1 ≤ L'.1) :
    a L ≫ pullback.snd _ _ = (a L' ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  rw [← ha L L' h, Category.assoc, tr_snd, Category.assoc]

include ha in
private theorem a_fst (L : FI k Ω) : a L ≫ pullback.fst _ _ = a bt ≫ pullback.fst _ _ := by
  have h : (bt : FI k Ω).1 ≤ L.1 := bot_le
  have e := tr_fst p h
  rw [← ha bt L h, Category.assoc, e]

private def sc : Cone ((Dg k Ω).op ⋙ Scheme.Spec) where
  pt := T
  π := { app := fun L => a L.unop ≫ pullback.snd _ _
         naturality := fun L L' f => (Category.id_comp _).trans (a_snd p a ha L'.unop L.unop (leOfHom f.unop)) }

private def hl [Algebra.IsAlgebraic k Ω] : IsLimit (Scheme.Spec.mapCone (cg k Ω).op) :=
  isLimitOfPreserves Scheme.Spec (cgColim k Ω).op

variable [Algebra.IsAlgebraic k Ω]

private def lf : T ⟶ Spec (CommRingCat.of Ω) := (hl (k := k) (Ω := Ω)).lift (sc p a ha)

private theorem lf_fac (L : FI k Ω) :
    lf p a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 Ω)) = a L ≫ pullback.snd _ _ :=
  (hl (k := k) (Ω := Ω)).fac (sc p a ha) (op L)

private theorem lf_uniq (m : T ⟶ Spec (CommRingCat.of Ω))
    (hm : ∀ L : FI k Ω, m ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 Ω)) = a L ≫ pullback.snd _ _) :
    m = lf p a ha :=
  (hl (k := k) (Ω := Ω)).uniq (sc p a ha) m fun L => hm L.unop

private theorem lf_cond : (a bt ≫ pullback.fst _ _) ≫ p =
    lf p a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap (bt (k := k) (Ω := Ω)).1 Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (bt (k := k) (Ω := Ω)).1)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [e, ← Category.assoc, lf_fac, Category.assoc, Category.assoc, pullback.condition]

private def gl : T ⟶ geom Ω p := pullback.lift (a bt ≫ pullback.fst _ _) (lf p a ha) (lf_cond p a ha)

private theorem gl_fst : gl p a ha ≫ pullback.fst _ _ = a bt ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

private theorem gl_snd : gl p a ha ≫ pullback.snd _ _ = lf p a ha := pullback.lift_snd _ _ _

private theorem gl_fac (L : FI k Ω) : gl p a ha ≫ LateralTheory.EWeil.StabPf.proj L.1 p = a L := by
  apply pullback.hom_ext
  · rw [Category.assoc, pj_fst, gl_fst]
    exact (a_fst p a ha L).symm
  · rw [Category.assoc, pj_snd, ← Category.assoc, gl_snd, lf_fac]

private theorem gl_uniq (m : T ⟶ geom Ω p) (hm : ∀ L : FI k Ω, m ≫ LateralTheory.EWeil.StabPf.proj L.1 p = a L) :
    m = gl p a ha := by
  apply pullback.hom_ext
  · rw [gl_fst, ← hm bt, Category.assoc, pj_fst]
  · rw [gl_snd]
    refine lf_uniq p a ha _ fun L => ?_
    rw [← hm L, Category.assoc, Category.assoc, pj_snd]

end Lim

private def cnLim [Algebra.IsAlgebraic k Ω] : IsLimit (cn k Ω p) where
  lift s := gl p (fun L => s.π.app (op L)) fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op
  fac s L := gl_fac p (fun L => s.π.app (op L)) (fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op) L.unop
  uniq s m hm := gl_uniq p (fun L => s.π.app (op L)) (fun L L' h => s.w (homOfLE (show L ≤ L' from h)).op) m
    fun L => hm (op L)

private theorem gd_compact (hqc : QuasiCompact p) (L : IntermediateField k Ω) : CompactSpace (geom L p) := by
  haveI : QuasiCompact (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _) hqc
  exact QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

private theorem gd_qs (hqs : QuasiSeparated p) (L : IntermediateField k Ω) : QuasiSeparatedSpace (geom L p) := by
  haveI : QuasiSeparated (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback _ _) hqs
  exact quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))

private theorem tr_affine {L L' : IntermediateField k Ω} (h : L ≤ L') : IsAffineHom (tr p h) := by
  have e : Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k L)) = Spec.map (CommRingCat.ofHom (algebraMap k L')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hsq : IsPullback (tr p h) (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L'))))
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap k L))) (v₁₃ := p) ?_ (tr_snd p h)
      (IsPullback.of_hasPullback _ _)
    rw [tr_fst, e]
    exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip (isAffineHom_of_isAffine _)

end Geo

end UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits

open UpperTheory.Gal.Int.Geo.HeightDescentDirectedColimits in
theorem UpperTheory.Gal.Int.Geo.htDesc_of :
    HtDesc := by
  intro q k Ω _ _ _ _ X p hqc hqs n i y
  obtain ⟨L, z, hz⟩ := (GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) _ (Gd k Ω p) (cn k Ω p) (cnLim p)
    (fun L => gd_compact p hqc L.unop.1) (fun L => gd_qs p hqs L.unop.1) (fun _ _ f => tr_affine p (leOfHom f.unop)) n).1 y
  exact ⟨L.unop.1, L.unop.2, z, hz⟩
