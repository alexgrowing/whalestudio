import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitCompsOfIsTowerOf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed Xo c) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
