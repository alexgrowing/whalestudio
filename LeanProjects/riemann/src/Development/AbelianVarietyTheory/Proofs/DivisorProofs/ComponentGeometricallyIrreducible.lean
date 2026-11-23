import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpacePullbackFieldOfIrreducibleCoverStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

noncomputable section
namespace GlobalTheory.GeomIrrComp

theorem residue_germ_injective {X : Scheme.{0}} [IsReduced X] (V : X.Opens) (x : X) (hx : x ∈ V)
    (hgen : ∀ y ∈ V, x ⤳ y) : Function.Injective (X.presheaf.germ V x hx ≫ X.residue x).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro y hy
  have hxy := hgen y (X.basicOpen_le s hy)
  have hxb : x ∈ X.basicOpen s := hxy.mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen _ _ _ hx] at hxb
  exfalso
  have := hxb.map (X.residue x).hom
  rw [CommRingCat.comp_apply] at hs
  rw [hs] at this
  exact not_isUnit_zero this

theorem residue_comp_appTop {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (x : X) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x =
      Spec.preimage (X.fromSpecResidueField x ≫ g) := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  simp only [Spec.map_comp, Category.assoc]
  rw [← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Scheme.fromSpecResidueField, Category.assoc]

theorem irreducibleSpace_pullback_of_isDomain {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F)
    (V : X.Opens) (hV : IsAffineOpen V) (k : Type) [Field k] (f : F →+* k) :
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) :=
  GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor g V hV k f

theorem irreducibleSpace_pullback_of_cover {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F)
    (k : Type) [Field k] (f : F →+* k) (U : X.Opens) (hU : IsIrreducible (U : Set X))
    (hV : ∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) :
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) :=
  GlobalTheory.T.irreducibleSpace_pullback_field_of_irreducible_cover h k f U hU hV

theorem irreducibleSpace_pullback_affine {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (V : X.Opens) (hV : IsAffineOpen V) (hx : x ∈ V) (hgen : ∀ y ∈ V, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by
  let φ : CommRingCat.of F ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op
  letI : Algebra F Γ(X, V) := φ.hom.toAlgebra
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
  letI : Algebra F k := f.toAlgebra
  have hft : Algebra.FiniteType F Γ(X, V) := by
    have h1 : (g.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨⊤, isAffineOpen_top (Sp F)⟩ ⟨V, hV⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2
    have e : φ = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appLE ⊤ V le_top := by
      simp [φ, Scheme.Hom.appLE]
    have h3 : φ.hom.FiniteType := by rw [e]; exact h1.comp h2
    exact h3
  let j : Γ(X, V) →ₐ[F] X.residueField x :=
    { toRingHom := (X.presheaf.germ V x hx ≫ X.residue x).hom
      commutes' := fun c => by
        have e := congrArg (fun m => m.hom c) (residue_comp_appTop g x)
        have e2 : φ ≫ X.presheaf.germ V x hx ≫ X.residue x = (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫
            g.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
          simp [φ]
        change (φ ≫ X.presheaf.germ V x hx ≫ X.residue x).hom c = _
        rw [e2]
        exact e }
  have hd := GlobalTheory.GeomConn.isDomain_tensor j (residue_germ_injective V x hx hgen) hac k
  exact irreducibleSpace_pullback_of_isDomain g V hV k f hd

theorem irreducibleSpace_pullback {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Sp F) [LocallyOfFiniteType g] (x : X)
    (hac : letI := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
      ∀ a : X.residueField x, IsAlgebraic F a → a ∈ (algebraMap F (X.residueField x)).range)
    (U : X.Opens) (hx : x ∈ U) (hgen : ∀ y ∈ U, x ⤳ y)
    (k : Type) [Field k] (f : F →+* k) : IrreducibleSpace ↑(pullback (U.ι ≫ g) (spMap f)) := by
  have hU : IsIrreducible (U : Set X) := by
    have hc : closure (U : Set X) = closure {x} := by
      apply le_antisymm
      · rw [isClosed_closure.closure_subset_iff]
        exact fun y hy => specializes_iff_mem_closure.mp (hgen y hy)
      · exact closure_mono (Set.singleton_subset_iff.mpr hx)
    rw [← isIrreducible_iff_closure, hc]
    exact isIrreducible_singleton.closure
  refine irreducibleSpace_pullback_of_cover g k f U hU fun y hy => ?_
  obtain ⟨V, hVa, hyV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hy
  refine ⟨V, hVU, hyV, irreducibleSpace_pullback_affine g x hac V hVa ((hgen y hy).mem_open V.isOpen hyV)
    (fun z hz => hgen z (hVU hz)) k f⟩

theorem algClosed_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hac : FnAlgClosed Xo c) (Z : Comp Xo c)
    (a : kap Z) (ha : IsAlgebraic c.F a) : a ∈ (algebraMap c.F (kap Z)).range := by
  have hb : IsAlgebraic c.F (algebraMap (kap Z) (Om Z) a) := ha.algebraMap
  obtain ⟨b, hb'⟩ := hac Z _ hb
  refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  exact hb'

end GlobalTheory.GeomIrrComp

open GlobalTheory.GeomIrrComp in

theorem GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), FnAlgClosed Xo c → ∀ Z : Comp Xo c,
    ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f)) := by
  intro E _ _ _ H Dw l Xo c hac Z
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  haveI : Smooth (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.isNormalScheme_of_smooth strK
  haveI : LocallyOfFiniteType (strK (Xo := Xo) (c := c)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) := LocallyOfFiniteType.isLocallyNoetherian strK
  haveI : IsReduced (Xo.XF c) := GlobalTheory.IsNormalScheme.isReduced
  refine ⟨GlobalTheory.IsNormalScheme.component Z, rfl, fun k _ f => ?_⟩
  have hZc : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hg : IsGenericPoint (genPt Z) (Z : Set (Xo.XF c)) := by
    have := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  exact irreducibleSpace_pullback strK (genPt Z) (fun a ha => algClosed_kap hac Z a ha)
    (GlobalTheory.IsNormalScheme.component Z) hg.mem (fun y hy => hg.specializes hy) k f
