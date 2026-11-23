import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

theorem exists_finite_torusExtension_act : ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω))
    [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G')
    (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
    IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
        (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
        (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
        IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
        (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  intro O _ K Ω _ _ _ _ G _ hG i G' _ i' φ hφ X _ _ _ u' A _ q' j hA hu hk hq
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.separated

  let T' : TorusExtension G' :=
    { X := X, B := A, isAbelian := hA, q := q', q_hom := hk.1, q_flat := hk.2.1, q_surjective := hk.2.2.1,
      q_quasiCompact := hk.2.2.2.1, i := u', i_hom := hu, isKernel := hk.2.2.2.2 }
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ.1 (isGrpPullback_pullback G (spMap (algebraMap K Ω)))
  haveI := he
  obtain ⟨F, hF, ⟨T₀⟩⟩ := GlobalTheory.exists_finite_torusExtension K Ω G inferInstance inferInstance inferInstance
    ⟨torusExtOfIso e T'⟩
  letI := T₀.addCommGroup
  letI := T₀.grpB
  have := T₀.free
  have := T₀.finite
  have := T₀.isAbelian.proper
  have := T₀.isAbelian.comm
  have := T₀.i_hom
  have := T₀.q_hom

  let i₀ : OAct O ((Over.pullback (spMap (algebraMap K F))).obj G) := OAct.pullback _ G i
  have h₀ : IsActPull i₀ i (spMap (algebraMap K F)) (pullback.fst G.hom _) := exists_isActPull _ i
  have hk₀ : IsKer T₀.i T₀.q := isKer_torusExtension T₀
  have hu₀ : ∀ a, T₀.i ≫ i₀.act a ≫ T₀.q = toUnit _ ≫ η[T₀.B] := fun a => by
    have := i₀.hom a
    rw [GlobalTheory.SemiRigid.torus_const T₀.X T₀.B (T₀.i ≫ i₀.act a ≫ T₀.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  obtain ⟨j₀, hj₀⟩ := hk₀.exists_oAct i₀ hu₀

  let f := spMap (algebraMap F Ω)
  have hf : f ≫ spMap (algebraMap K F) = spMap (algebraMap K Ω) :=
    FieldModel.spMap_comp (IsScalarTower.algebraMap_eq K F Ω).symm
  obtain ⟨φ', eφ', Hφ'⟩ := FieldModel.exists_baseChange (X₀ := G) hf hφ.1.1
  have gp : IsGrpPullback G' ((Over.pullback (spMap (algebraMap K F))).obj G) f φ' :=
    (isGrpPullback_pullback G _).cancel (hφ.1.congr hf.symm eφ'.symm) Hφ'.w
  have hact : ∀ a, (i'.act a).left ≫ φ' = φ' ≫ (i₀.act a).left := fun a => by
    refine (isGrpPullback_pullback G (spMap (algebraMap K F))).1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, eφ', h₀.2 a, ← Category.assoc, eφ']
      exact hφ.2 a
    · rw [Category.assoc, Category.assoc, Over.w (i₀.act a), Hφ'.w, ← Category.assoc, Over.w (i'.act a)]

  obtain ⟨u'', hu'', -⟩ := existsUnique_torusCompat gp.1 T₀.i
  have : IsMonHom u'' := TorusCompat.isMonHom gp hu''
  obtain ⟨q'', hk'', hsq⟩ := IsKer.baseChange gp (isGrpPullback_pullback T₀.B f) hu'' hk₀
  have := hA.proper
  have hBp : IsProper ((Over.pullback f).obj T₀.B).hom := by
    show IsProper (pullback.snd T₀.B.hom f); infer_instance
  have := hk''.1
  have := hk.1
  have c₁ : u'' ≫ q' = toUnit _ ≫ η[A] := by
    rw [GlobalTheory.SemiRigid.torus_const T₀.X A (u'' ≫ q')]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  have c₂ : u' ≫ q'' = toUnit _ ≫ η[(Over.pullback f).obj T₀.B] := by
    rw [GlobalTheory.SemiRigid.torus_const X _ (u' ≫ q'')]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  obtain ⟨β, hβ, hβq⟩ := flatQuotient_iso_of_same_kernel _ G' _ A _ _ q'' u'' q' u' hk''.1 inferInstance hk''.2.1
    hk''.2.2.1 hk''.2.2.2.1 hk''.2.2.2.2 hk.1 hu hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2 c₂ c₁
  haveI := hβ

  let jω : OAct O ((Over.pullback f).obj T₀.B) := OAct.pullback f T₀.B j₀
  have e1 : ∀ a, (i'.act a).left ≫ q''.left ≫ pullback.fst T₀.B.hom f =
      q''.left ≫ pullback.fst T₀.B.hom f ≫ (j₀.act a).left := fun a => by
    have h1 := congrArg CommaMorphism.left (hj₀ a)
    simp only [Over.comp_left] at h1
    rw [← hsq.w, reassoc_of% (hact a), h1]
    exact (reassoc_of% hsq.w) _
  have key : ∀ a, i'.act a ≫ q'' = q'' ≫ jω.act a := fun a => by
    apply Over.OverMorphism.ext
    refine (isGrpPullback_pullback T₀.B f).1.hom_ext ?_ ?_
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, (exists_isActPull f j₀).2 a]
      exact e1 a
    · exact (Over.w _).trans (Over.w _).symm
  have := hk.2.1
  have := hk.2.2.1
  haveI : Epi q' := FlatQuotient.epi_of_flat_surjective q'
  have key2 : ∀ a, j.act a ≫ β.hom = β.hom ≫ jω.act a := fun a => by
    rw [← cancel_epi q', ← reassoc_of% (hq a), hβq, reassoc_of% hβq]
    exact key a
  refine ⟨F, hF, _, inferInstance, i₀, pullback.fst G.hom _, T₀.X, T₀.addCommGroup, T₀.free, T₀.finite, T₀.i, T₀.B,
    T₀.grpB, T₀.q, j₀, β.hom.left ≫ pullback.fst T₀.B.hom f, h₀, T₀.isAbelian, T₀.i_hom, hk₀, hj₀, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback T₀.B f)).congr (Category.id_comp f) rfl
  · intro a
    have k3 := congrArg CommaMorphism.left (key2 a)
    simp only [Over.comp_left] at k3
    rw [reassoc_of% k3, (exists_isActPull f j₀).2 a, Category.assoc]

end GlobalTheory.TorusPart
