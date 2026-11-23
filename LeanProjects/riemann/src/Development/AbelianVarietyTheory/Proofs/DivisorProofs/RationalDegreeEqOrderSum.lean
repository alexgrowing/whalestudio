import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGeneric
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem flat_fst {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) : Flat (ratFibre.fst p) := by
  have h2 : Flat (spMap (Int.castRingHom ℚ)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ?_
    change Module.Flat ℤ ℚ
    exact IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h2

theorem isIso_stalkMap_and_injective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), (∀ y : ratFibre p, IsIso ((ratFibre.fst p).stalkMap y)) ∧ Function.Injective (ratFibre.fst p) := by
  intro k _ X p
  have h1 : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have h3 : IsPreimmersion (ratFibre.fst p) := MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h1
  have h4 := flat_fst p
  exact ⟨fun y => GenSpread.isIso_stalkMap_of_flat _ y, (ratFibre.fst p).isEmbedding.injective⟩

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

theorem fst_genericPoint : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] [IsIntegral (ratFibre p)], ratFibre.fst p (genericPoint (ratFibre p)) = genericPoint X := by
  intro k _ X p _ _
  have := flat_fst p
  obtain ⟨z, hz, e⟩ := Flat.generalizingMap (ratFibre.fst p)
    (genericPoint_specializes (ratFibre.fst p (genericPoint (ratFibre p))))
  rw [← e, (hz.antisymm (genericPoint_specializes z)).eq]

theorem exists_finset_zeros : ∀ (K : Type) [Field K] (C : Scheme.{0}) [Algebra K Γ(C, ⊤)] [IsIntegral C], IsProjCurve K C → ∀ (L : LB C) (s : L.Sec), genericPoint C ∈ nonzeroLocus s → ∃ S : Finset C, (∀ y : C, y ∉ nonzeroLocus s → y ∈ S) ∧ ∀ y ∈ S, IsClosed ({y} : Set C) := by
  intro K _ C _ _ hC L s hs
  classical
  have := hC.isNoetherian
  have hZ : IsClosed ((nonzeroLocus s : Set C)ᶜ) := (nonzeroLocus s).isOpen.isClosed_compl
  have hfin := GlobalTheory.ProperCurve.finite_of_isClosed hC.dim_eq hZ (fun h => h hs)
  refine ⟨hfin.toFinset, fun y hy => hfin.mem_toFinset.2 hy, fun y hy => ?_⟩
  refine GlobalTheory.ProperCurve.isClosed_singleton hC.dim_eq ?_
  rintro rfl
  exact (hfin.mem_toFinset.1 hy) hs

theorem nonempty_residueField_equiv : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (y : Y), IsIso (f.stalkMap y) → Nonempty (X.residueField (f y) ≃+* Y.residueField y) := by
  intro X Y f y h
  exact ⟨(IsLocalRing.ResidueField.mapEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv)⟩

theorem residueDegree_eq_card : ∀ (C : Scheme.{0}) [Algebra ℚ Γ(C, ⊤)], IsProjCurve ℚ C → ∀ y : C, IsClosed ({y} : Set C) → Finite (C.residueField y →+* ℂ) ∧ (strHom ℚ C).residueDegree y = Nat.card (C.residueField y →+* ℂ) := by
  intro C _ hC y hy
  have := hC.isProperCurve.isProper
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (strHom ℚ C)
  have h₁ : LocallyOfFiniteType (C.fromSpecResidueField y) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hy
  generalize strHom ℚ C = f at *
  rw [residueDegree_eq_finrank]
  letI := algebraΓOfHom f
  letI := residueFieldAlgebraOver ℚ y
  have : CharZero (C.residueField y) := algebraRat.charZero _
  have hft : Algebra.FiniteType ℚ (C.residueField y) := by
    have e : C.fromSpecResidueField y ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (C.residueField y))) := by
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (C.fromSpecResidueField y ≫ f)
      rw [← hφ]
      congr 1
      ext1
      exact Subsingleton.elim _ _
    have h : LocallyOfFiniteType (C.fromSpecResidueField y ≫ f) :=
      MorphismProperty.comp_mem @LocallyOfFiniteType _ _ h₁ inferInstance
    rw [e] at h
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h)
  have hf : Module.Finite ℚ (C.residueField y) := finite_of_finite_type_of_isJacobsonRing _ _
  have : NumberField (C.residueField y) := { to_finiteDimensional := by convert hf; exact Subsingleton.elim _ _ }
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  congr!
  exact Subsingleton.elim _ _

theorem isWeaklyRegular_germ : ∀ (Y : Scheme.{0}) [IsIntegral Y] (L : LB Y) (s : L.Sec), genericPoint Y ∈ nonzeroLocus s → ∀ (y : Y) (J : L.ι) (hJ : y ∈ L.U J), RingTheory.Sequence.IsWeaklyRegular ((QCoh.structureModule Y).presheaf.stalk y :) [Y.presheaf.germ _ y hJ (s.f J)] := by
  intro Y _ L s hs y J hJ
  refine ((QCoh.structureModuleStalkEquiv y).isWeaklyRegular_congr _).2 ?_
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  have hη : genericPoint Y ∈ L.U J := (genericPoint_specializes y).mem_open (L.U J).isOpen hJ
  have hu := (Y.mem_basicOpen _ _ hη).1 ((Cartier.mem_nonzeroLocus_iff s _ hη).1 hs)
  have h0 : Y.presheaf.germ _ y hJ (s.f J) ≠ 0 := fun h => by
    have : s.f J = 0 := germ_injective_of_isIntegral Y y hJ (h.trans (map_zero _).symm)
    rw [this, map_zero] at hu
    exact not_isUnit_zero hu
  exact (IsRegular.of_ne_zero h0).left.isSMulRegular

theorem length_eq_secOrd : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB X) (hL : L.IsLB) (s : L.Sec) (y : Y), IsIso (f.stalkMap y) → ∀ (J : (L.pull f).ι) (hJ : y ∈ (L.pull f).U J), (Module.length (Y.presheaf.stalk y) (((QCoh.structureModule Y).presheaf.stalk y :) ⧸ (Ideal.ofList [Y.presheaf.germ _ y hJ ((secPull s f).f J)] • ⊤ : Submodule (Y.presheaf.stalk y) ((QCoh.structureModule Y).presheaf.stalk y :)))).toNat = secOrd hL s (f y) := by
  intro X Y f L hL s y h J hJ
  have hi : f y ∈ L.U (J PUnit.unit) := mem_pull.1 hJ
  have e : Y.presheaf.germ _ y hJ ((secPull s f).f J) =
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv (X.presheaf.germ _ _ hi (s.f (J PUnit.unit))) :=
    (Y.presheaf.germ_res_apply _ y hJ _).trans (Scheme.Hom.germ_stalkMap_apply f _ y hi _).symm
  rw [secOrd_eq hL s hi, germOrd, ← ord_map_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv, ← e,
    Ring.ord, (Submodule.Quotient.equiv _ (Ideal.span {Y.presheaf.germ _ y hJ ((secPull s f).f J)})
      (QCoh.structureModuleStalkEquiv y) (by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, smul_eq_mul, Ideal.mul_top,
          Ideal.ofList_singleton])).length_eq]

theorem ratDeg_eq_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsProjCurve ℚ (ratFibre p) → ∀ (L : LB X) (hL : L.IsLB) (s : L.Sec), genericPoint X ∈ nonzeroLocus s → ∃ S : Finset X, (∀ x : X, CharZero (X.residueField x) → x ∉ nonzeroLocus s → x ∈ S) ∧ (∀ x ∈ S, Finite (X.residueField x →+* ℂ)) ∧ ratDeg p L = ∑ x ∈ S, (secOrd hL s x : ℤ) * (Nat.card (X.residueField x →+* ℂ) : ℤ) := by
  intro k _ X p _ hC L hL s hs
  classical
  have := hC.isIntegral
  obtain ⟨hiso, hinj⟩ := isIso_stalkMap_and_injective k X p
  have hL' : (L.pull (ratFibre.fst p)).IsLB := Semi.LB.isLB_pull hL _
  have hnz : ∀ y, y ∈ nonzeroLocus (secPull s (ratFibre.fst p)) ↔ ratFibre.fst p y ∈ nonzeroLocus s :=
    fun y => by rw [nonzeroLocus_secPull]; rfl
  have hs' : genericPoint (ratFibre p) ∈ nonzeroLocus (secPull s (ratFibre.fst p)) :=
    (hnz _).2 (by rw [fst_genericPoint k X p]; exact hs)
  obtain ⟨S', hS'z, hS'c⟩ := exists_finset_zeros ℚ (ratFibre p) hC _ _ hs'
  have hcard : ∀ y ∈ S', Finite (X.residueField (ratFibre.fst p y) →+* ℂ) ∧
      (ratFibre.snd p).residueDegree y = Nat.card (X.residueField (ratFibre.fst p y) →+* ℂ) := by
    intro y hy
    obtain ⟨e⟩ := nonempty_residueField_equiv X (ratFibre p) (ratFibre.fst p) y (hiso y)
    let E : (X.residueField (ratFibre.fst p y) →+* ℂ) ≃ ((ratFibre p).residueField y →+* ℂ) :=
      { toFun := fun g => g.comp e.symm.toRingHom
        invFun := fun g => g.comp e.toRingHom
        left_inv := fun g => by ext a; simp
        right_inv := fun g => by ext a; simp }
    obtain ⟨h₁, h₂⟩ := residueDegree_eq_card (ratFibre p) hC y (hS'c y hy)
    refine ⟨Finite.of_equiv _ E.symm, ?_⟩
    rw [← ratFibre.strHom_eq p, h₂, Nat.card_congr E]
  refine ⟨S'.image (ratFibre.fst p), ?_, ?_, ?_⟩
  · intro x hx hxs
    obtain ⟨y, rfl⟩ := mem_range_fst k X p x hx
    exact Finset.mem_image_of_mem _ (hS'z y ((hnz y).not.2 hxs))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact (hcard y hy).1
  · let c : ratFibre p → (L.pull (ratFibre.fst p)).ι := fun y _ => (exists_mem_chart hL (ratFibre.fst p y)).choose
    have hc : ∀ y, y ∈ (L.pull (ratFibre.fst p)).U (c y) := fun y =>
      mem_pull.2 (exists_mem_chart hL (ratFibre.fst p y)).choose_spec
    have hP : IsProjOver (ratFibre.snd p) := by
      have := hC.isProjOver
      rwa [ratFibre.strHom_eq p] at this
    have key := CutDegree.interNum_eq_sum_length (ratFibre.snd p) hP hL' c hc S' hS'c
      [secPull s (ratFibre.fst p)] (QCoh.structureModule (ratFibre p))
      (fun y _ hy => hS'z y (hy _ (List.mem_singleton_self _)))
      (fun y _ => isWeaklyRegular_germ (ratFibre p) _ _ hs' y (c y) (hc y))
    have e1 : (fun _ : Fin [secPull s (ratFibre.fst p)].length => L.pull (ratFibre.fst p)) = ![L.pull (ratFibre.fst p)] :=
      funext fun i => by fin_cases i; rfl
    rw [e1] at key
    rw [ratDeg_eq_degLB hL, hC.degLB_eq_interNum hL', key, Finset.sum_image (fun a _ b _ h => hinj h)]
    push_cast
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(hcard y hy).2]
    congr 2
    exact length_eq_secOrd X (ratFibre p) (ratFibre.fst p) L hL s y (hiso y) (c y) (hc y)

end GlobalTheory.RatDegZeros
