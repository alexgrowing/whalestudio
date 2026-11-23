import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.CA (IsCM)
open GlobalTheory.Adelic (cutIdeal mem_support_cutIdeal)
open GlobalTheory.QCoh GlobalTheory.Vanishing RingTheory.Sequence

namespace GlobalTheory.Published

def ProperIntersectionLength : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (D : ℕ), IsProjOver f →
    topologicalKrullDim X = D → ∀ (L : LB X) (hL : L.IsLB) (s : Fin D → L.Sec),
    ((cutIdeal hL s).support : Set X).Finite →
    (∀ y ∈ (cutIdeal hL s).support, IsCM (X.presheaf.stalk y)) →
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤)

end GlobalTheory.Published

namespace GlobalTheory.ProperCut

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k)

theorem ringKrullDim_stalk_eq [IsIntegral X] [LocallyOfFiniteType f] {x : X} (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim_stalk_eq_coheight]
    exact (Order.coheight_le_krullDim x).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).ge
  obtain ⟨A, _, _, _, _, _, j, _, ⟨q, rfl⟩, -, hA⟩ := exists_affine_chart_trdeg_eq f x
  obtain ⟨d, -, hd⟩ := exists_ringKrullDim_eq_and_trdeg_eq k A
  have hq : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).1 (by
    have := hx.preimage j.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ j.isOpenEmbedding.injective] at this)
  rw [ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of A) q).commRingCatIsoToRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal),
    ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field d hd]
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨B, _, _, _, _, _, i, _, hy, -, hB⟩ := exists_affine_chart_trdeg_eq f y
  refine ⟨_, i.isOpenEmbedding.isOpen_range, hy, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
  exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := B)).trans
    (ringKrullDim_eq_of_trdeg_eq k B (hB.trans (hA.symm.trans hd)))).le

theorem discreteTopology_subscheme [LocallyOfFiniteType f] (I : X.IdealSheafData) (h : (I.support : Set X).Finite) :
    Finite I.subscheme ∧ DiscreteTopology I.subscheme := by
  have : Finite I.subscheme := Set.finite_univ_iff.1 <| Set.Finite.of_finite_image
    (by rwa [Set.image_univ, I.range_subschemeι]) I.subschemeι.isClosedEmbedding.injective.injOn
  have : JacobsonSpace I.subscheme := LocallyOfFiniteType.jacobsonSpace (I.subschemeι ≫ f)
  exact ⟨‹_›, JacobsonSpace.discreteTopology (Set.toFinite _)⟩

theorem isClosed_singleton_of_finite [LocallyOfFiniteType f] (I : X.IdealSheafData) (h : (I.support : Set X).Finite)
    {y : X} (hy : y ∈ I.support) : IsClosed ({y} : Set X) := by
  obtain ⟨z, rfl⟩ := exists_ι_eq hy
  have := (discreteTopology_subscheme f I h).2
  simpa using I.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete {z})

theorem residueDegree_of_isClosedImmersion {Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) :
    i.residueDegree y = 1 := by
  letI := (i.residueFieldMap y).hom.toAlgebra
  refine Module.finrank_of_bijective_algebraMap ⟨(i.residueFieldMap y).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Y.residue_surjective y a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective y b
  exact ⟨X.residue _ c, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i y) c⟩

theorem topSelf_eq_length {D : ℕ} (hf : IsProjOver f) {L : LB X} (hL : L.IsLB) (s : Fin D → L.Sec)
    (hfin : ((cutIdeal hL s).support : Set X).Finite)
    (hCM : ∀ y ∈ (cutIdeal hL s).support, IsCM (X.presheaf.stalk y))
    (hD : ∀ y ∈ (cutIdeal hL s).support, (D : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk y)) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤) := by
  classical
  letI := algebraΓOfHom f
  letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
  have := isNoetherian_of_isProjOver hf
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  have hker : ∀ (z : (cutIdeal hL s).subscheme) (c : L.ι) (hc : (cutIdeal hL s).subschemeι z ∈ L.U c),
      Ideal.ofList (List.ofFn fun i => X.presheaf.germ (L.U c) _ hc ((s i).f c)) =
        RingHom.ker ((cutIdeal hL s).subschemeι.stalkMap z).hom := fun z c hc =>
    (ofList_ofFn_eq_span_range _).trans ((ker_stalkMap _ z).trans (stalkId_cutIdeal hL s c _ hc)).symm
  have hmem := mem_support_cutIdeal hL s
  generalize cutIdeal hL s = I at *
  obtain ⟨_, _⟩ := discreteTopology_subscheme f I hfin
  letI := Fintype.ofFinite I.subscheme
  have hV : topologicalKrullDim I.subscheme ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  have : IsLocallyArtinian I.subscheme := .of_topologicalKrullDim_le_zero hV
  have : IsArtinianScheme I.subscheme := {}
  have hfi : IsFinite (I.subschemeι ≫ f) :=
    have : LocallyQuasiFinite (I.subschemeι ≫ f) := .of_finite_preimage_singleton _ fun _ => Set.toFinite _
    .of_locallyQuasiFinite _
  have hs : suppDim (QCoh.structureModule I.subscheme) ≤ 0 := suppDim_structureModule.trans_le hV
  have hlen : ∀ z : I.subscheme, IsFiniteLength (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z) :=
    fun z => (structureModuleStalkEquiv z).isFiniteLength (isFiniteLength_stalk hs z)
  have hreg : ∀ y ∈ I.support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c)) := by
    intro y hy c hc
    obtain ⟨z, rfl⟩ := exists_ι_eq hy
    refine isRegular_of_isCM_of_ringKrullDim_quotient_add_length_le (hCM _ hy) (fun a ha => ?_) ?_
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) ((hker z c hc).le (Ideal.subset_span ha))
    · have : IsArtinianRing (I.subscheme.presheaf.stalk z) :=
        (isFiniteLength_iff_isNoetherian_isArtinian.1 (hlen z)).2
      rw [hker, ringKrullDim_eq_of_ringEquiv
        (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z)),
        ringKrullDimZero_iff_ringKrullDim_eq_zero.1 inferInstance, zero_add, List.length_ofFn]
      exact hD _ hy
  have hsum : topSelfIntersection k L D = (∑ z : I.subscheme, (I.subschemeι ≫ f).residueDegree z *
      (Module.length (I.subscheme.presheaf.stalk z) (I.subscheme.presheaf.stalk z)).toNat : ℕ) := by
    choose c hc using Semi.LB.mem_of_cover hL
    have key := CutDegree.interNum_eq_sum_length f hf hL c hc (Finset.univ.image I.subschemeι) (fun x hx => ?_)
      (List.ofFn s) (structureModule X) (fun x _ hx => ?_) fun x hx => ?_
    · have e : topSelfIntersection k L D = topSelfIntersection k L (List.ofFn s).length := by rw [List.length_ofFn]
      rw [e, topSelf_def, key, Finset.sum_image I.subschemeι.isClosedEmbedding.injective.injOn]
      refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
      rw [CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion I.subschemeι, mul_one,
        mul_comm, List.map_ofFn]
      refine congrArg (_ * ENat.toNat ·) ?_
      letI := (I.subschemeι.stalkMap z).hom.toAlgebra
      rw [← Module.length_eq_of_surjective (S := X.presheaf.stalk (I.subschemeι z))
        (I.subschemeι.stalkMap_surjective z)]
      refine (Submodule.Quotient.equiv _ (LinearMap.ker (Algebra.linearMap _ (I.subscheme.presheaf.stalk z)))
        (structureModuleStalkEquiv _) ?_).length_eq.trans
        (LinearMap.quotKerEquivOfSurjective _ (I.subschemeι.stalkMap_surjective z)).length_eq
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, smul_eq_mul, Ideal.mul_top]
      exact hker z _ _
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
      exact isClosed_singleton_of_finite f I hfin (ι_mem_support I z)
    · obtain ⟨z, rfl⟩ := exists_ι_eq ((hmem x).2 fun i => hx _ (List.mem_ofFn.2 ⟨i, rfl⟩))
      exact Finset.mem_image_of_mem _ (Finset.mem_univ z)
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
      rw [List.map_ofFn]
      exact ((structureModuleStalkEquiv _).isWeaklyRegular_congr _).2
        (hreg _ (ι_mem_support I z) _ _).toIsWeaklyRegular
  refine ⟨hfi, hreg, fun z => Module.length_ne_top_iff.2 (hlen z), by rw [finsum_eq_sum_of_fintype, hsum],
    ((I.subschemeι ≫ f).finite_appTop).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2), ?_⟩
  rw [hsum, ← ((coh.zeroUnitEquiv I.subscheme).restrictScalars k).finrank_eq]
  refine congrArg _ (Eq.trans ?_ (hdim_zero_eq_sum_toNat (I.subschemeι ≫ f) hs (S := Finset.univ) (by simp)).symm)
  exact Finset.sum_congr rfl fun z _ => by rw [mul_comm, (structureModuleStalkEquiv z).length_eq]

theorem isCM_stalk_of_smooth {D : ℕ} (hd : SmoothOfRelativeDimension D f) {y : X} (hy : IsClosed ({y} : Set X)) :
    IsCM (X.presheaf.stalk y) := by
  have := (StabFlat.stalk_of_smooth_local k X f D hd y hy _ (Spec.map_preimage _).symm inferInstance).2.2.1
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at this
  have := IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk y))
  exact isCM_of_isRegularLocalRing _

theorem topSelf_eq_length_of_smooth {D : ℕ} (hd : SmoothOfRelativeDimension D f) (hf : IsProjOver f) {L : LB X}
    (hL : L.IsLB) (s : Fin D → L.Sec) (hfin : ((cutIdeal hL s).support : Set X).Finite) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ f)
    IsFinite ((cutIdeal hL s).subschemeι ≫ f) ∧
    (∀ y ∈ (cutIdeal hL s).support, ∀ (c : L.ι) (hc : y ∈ L.U c),
      IsRegular (X.presheaf.stalk y) (List.ofFn fun i => X.presheaf.germ (L.U c) y hc ((s i).f c))) ∧
    (∀ z : (cutIdeal hL s).subscheme, Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
      ((cutIdeal hL s).subscheme.presheaf.stalk z) ≠ ⊤) ∧
    topSelfIntersection k L D = (∑ᶠ z : (cutIdeal hL s).subscheme, ((cutIdeal hL s).subschemeι ≫ f).residueDegree z *
      (Module.length ((cutIdeal hL s).subscheme.presheaf.stalk z)
        ((cutIdeal hL s).subscheme.presheaf.stalk z)).toNat : ℕ) ∧
    Module.Finite k Γ((cutIdeal hL s).subscheme, ⊤) ∧
    topSelfIntersection k L D = Module.finrank k Γ((cutIdeal hL s).subscheme, ⊤) := by
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  exact topSelf_eq_length f hf hL s hfin
    (fun y hy => isCM_stalk_of_smooth f hd (isClosed_singleton_of_finite f _ hfin hy))
    fun y hy => (CutDegree.ringKrullDim_stalk hd (isClosed_singleton_of_finite f _ hfin hy)).ge

end GlobalTheory.ProperCut

namespace GlobalTheory.Published

theorem ProperIntersectionLength_holds : ProperIntersectionLength := fun _ _ _ _ f _ hf hd _ hL s hfin hCM =>
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  ProperCut.topSelf_eq_length f hf hL s hfin hCM fun _ hy =>
    ((ProperCut.ringKrullDim_stalk_eq f (ProperCut.isClosed_singleton_of_finite f _ hfin hy)).trans hd).ge

example (h : ProperIntersectionLength) {F : Type} [Field F] (Y : ProjVar.Var F) (L : LB Y.X) (hL : L.IsLB)
    (s : Fin Y.dim → L.Sec) (hfin : ((cutIdeal hL s).support : Set Y.X).Finite) :
    letI := algebraΓOfHom Y.str
    letI := algebraΓOfHom ((cutIdeal hL s).subschemeι ≫ Y.str)
    topSelfIntersection F L Y.dim = Module.finrank F Γ((cutIdeal hL s).subscheme, ⊤) :=
  (h F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq L hL s hfin fun _ hy =>
    ProperCut.isCM_stalk_of_smooth Y.str Y.smooth_str
      (ProperCut.isClosed_singleton_of_finite Y.str _ hfin hy)).2.2.2.2.2

end GlobalTheory.Published
