import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_point {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, ∀ r, φ r = 0 → r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : e.symm (Ideal.Quotient.mk m r) = 0 := hr
  exact (map_eq_zero_iff e.symm e.symm.injective).mp h0

private theorem dom_fg {k R A ι : Type} [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing A] [IsDomain A] [Algebra k A] (e : Module.Basis ι k A)
    (s t : Finset ι) (a b : ι → R)
    (h : (∑ i ∈ s, a i ⊗ₜ[k] e i) * (∑ j ∈ t, b j ⊗ₜ[k] e j) = 0) :
    (∀ i ∈ s, a i = 0) ∨ (∀ j ∈ t, b j = 0) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩ := hcon
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hab : a i0 * b j0 ≠ 0 := mul_ne_zero ha hb
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors
  have hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson := by
    rw [hjac]
    simpa using hab
  obtain ⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by
    by_contra hne
    push_neg at hne
    apply hnot
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hne J hJ
  haveI := hm
  obtain ⟨φ, hφ⟩ := exists_point (k := k) m
  have hφa : φ (a i0) ≠ 0 := fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))
  have hφb : φ (b j0) ≠ 0 := fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))
  let ψ : R ⊗[k] A →ₐ[k] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : ι → R) (u : Finset ι),
      ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i := by
    intro c u
    simp [ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have h2 := congrArg ψ h
  rw [map_mul, hψ, hψ, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)
  · exact hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)

private theorem dom_tensor (k K L : Type) [Field k] [IsAlgClosed k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsDomain (L ⊗[k] K) := by
  classical
  let e := Module.Basis.ofVectorSpace k K
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  suffices hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  have hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i := by
    intro z
    conv_lhs => rw [← E.symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
  let S : Finset L := (E x).support.image (E x) ∪ (E y).support.image (E y)
  let R := Algebra.adjoin k (S : Set L)
  haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)
  have hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R := by
    rintro z hz i
    by_cases hi : i ∈ (E z).support
    · apply Algebra.subset_adjoin
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact R.zero_mem
  let a : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩
  let b : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩
  let j : R ⊗[k] K →ₐ[k] L ⊗[k] K := Algebra.TensorProduct.map R.val (AlgHom.id k K)
  have hj : Function.Injective j := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective
    exact this
  have hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x := by
    rw [map_sum]
    conv_rhs => rw [hrep x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, a]
  have hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y := by
    rw [map_sum]
    conv_rhs => rw [hrep y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, b]
  have hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0 := by
    apply hj
    rw [map_mul, hja, hjb, hxy, map_zero]
  rcases dom_fg (k := k) e _ _ a b hprod with h0 | h0
  · left
    rw [hrep x]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [a, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · right
    rw [hrep y]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [b, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]

private theorem gi (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := dom_tensor k K L
  let e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K)) := h.isoPullback ≪≫ pullbackSpecIso k L K
  haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

theorem UpperTheory.isCurve_pullback_of_isCurve_baseChange :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → IsCurve (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  intro k L _ _ _ _ C c hc
  obtain ⟨h1, h2, h3⟩ := hc
  haveI := gi k L
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  set p := pullback.fst c g with hp
  haveI : GeometricallyIrreducible p := inferInstance
  haveI : GeometricallyReduced p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Finite (irreducibleComponents C) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  haveI hred : IsReduced (pullback c g) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  set η := genericPoint C
  let ξ : ↥(pullback c g) := p.fiberι η (genericPoint (p.fiber η))
  have hall : ∀ q : ↥(pullback c g), ξ ⤳ q := by
    intro q
    have h0 : η ⤳ p q := genericPoint_specializes _
    obtain ⟨q', hq', hpq'⟩ := hgen h0
    have hmem : q' ∈ Set.range (p.fiberι η) := by
      rw [p.range_fiberι]
      exact hpq'
    obtain ⟨r, rfl⟩ := hmem
    exact ((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'
  haveI hirr : IrreducibleSpace ↥(pullback c g) := by
    rw [irreducibleSpace_def]
    have hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI := isSmoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3
