import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOfFlatSpecialFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibreStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinFlat

theorem bijective_of_lTensor (R M N : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (h : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) : Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have hQ : Subsingleton (IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f)) := by
      have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f), z = 0 := fun z => by
        obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (IsLocalRing.ResidueField R)
          (Submodule.mkQ_surjective (LinearMap.range f)) z
        obtain ⟨v, rfl⟩ := h.2 w
        have h0 : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
          ext x
          simp
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]
        rfl
      exact ⟨fun x y => by rw [key x, key y]⟩
    have h1 : Subsingleton (N ⧸ LinearMap.range f) := IsLocalRing.subsingleton_tensorProduct.1 hQ
    exact fun y => (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 (Subsingleton.elim _ _)
  have hfree : Module.Free R N := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ y, f (s y) = y := fun y => LinearMap.congr_fun hs y
  let π : M →ₗ[R] LinearMap.ker f := (LinearMap.id - s ∘ₗ f).codRestrict (LinearMap.ker f) (fun x => by
    simp [hs'])
  have hπ : π ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [π, LinearMap.mem_ker.1 x.2]
  have hK : Subsingleton (IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f) := by
    have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f, z = 0 := fun z => by
      have h0 : f ∘ₗ (LinearMap.ker f).subtype = 0 := by
        ext x
        simp
      have h1 : (LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z = 0 := by
        apply h.1
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero, map_zero]
        rfl
      have h2 : π.lTensor (IsLocalRing.ResidueField R) ((LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z) = z := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ, LinearMap.lTensor_id]
        rfl
      rw [← h2, h1, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  have hK' : Subsingleton (LinearMap.ker f) := IsLocalRing.subsingleton_tensorProduct.1 hK
  refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hsurj⟩
  have h3 : (⟨x, hx⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h3

theorem flat_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite A.hom] [IsFinite B.hom] [Flat A.hom] (b : A ⟶ B)
    (h : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Flat b.left := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R A B b
  have := h3 inferInstance
  have h' : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  rw [Flat.SpecMap_iff] at h'
  have h'' : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [Flat.SpecMap_iff]
    exact GlobalTheory.T.flat_of_flat_special_fibre R Q P φ h'
  rw [e1]; infer_instance

theorem isIso_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C K : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite K.hom] [Flat C.hom] (u : C ⟶ K)
    (h : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) : IsIso u := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R C K u
  have := h3 inferInstance
  have h0 : IsIso ((Over.forget _).map ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) := inferInstance
  have h0' : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left := h0
  have h' : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  have h2' : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) :=
    isIso_SpecMap_iff.1 h'
  have hco : ⇑(φ.toLinearMap.lTensor (IsLocalRing.ResidueField R)) =
      ⇑(Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ : Function.Bijective φ :=
    bijective_of_lTensor R Q P φ.toLinearMap (by rw [hco]; exact h2')
  have hS : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) := isIso_SpecMap_iff.2 hφ
  have hl : IsIso u.left := by rw [e1]; infer_instance
  haveI : IsIso ((Over.forget _).map u) := hl
  exact isIso_of_reflects_iso u (Over.forget _)

theorem surjective_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite B.hom] (b : A ⟶ B) [Flat b.left]
    (h : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Surjective b.left := by
  constructor
  intro x
  have hsp : SpecializingMap B.hom := B.hom.isClosedMap.specializingMap
  obtain ⟨y, hxy, hy⟩ := hsp (IsLocalRing.specializes_closedPoint (B.hom x))
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := by
    rw [Ideal.Quotient.nontrivial_iff]; simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))) := inferInstance
  have ht : thick R (IsLocalRing.maximalIdeal R) 0 t = IsLocalRing.closedPoint R := by
    have hle : IsLocalRing.maximalIdeal R ≤ (thick R (IsLocalRing.maximalIdeal R) 0 t).asIdeal := fun x hx => by
      show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)) x ∈ t.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hx)]
      exact zero_mem _
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (thick R (IsLocalRing.maximalIdeal R) 0 t).isPrime.ne_top) hle)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)
  obtain ⟨z₀, hz₀⟩ := h.surj y₀
  have hcomp : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) 0) =
      pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) ≫ b.left := pullback.lift_fst _ _ _
  have hz : b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) = y := by
    rw [← hy₀, ← hz₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨w, -, hw⟩ := Flat.generalizingMap b.left (show x ⤳ b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) by rwa [hz])
  exact ⟨w, hw⟩

theorem main (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (hab : a ≫ b = toUnit C ≫ e)
  (h₀ : IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e))
  (hf : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left)
  (hs : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) :
  IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  have hb : Flat b.left := flat_left_of_fibre R A B b hf
  have hK : IsPullback (pullback.fst b e) (toUnit (pullback b e)) b e := by
    have h := IsPullback.of_hasPullback b e
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  have hKl := hK.map (Over.forget _)
  have hKl' : IsPullback (pullback.fst b e).left (pullback b e).hom b.left e.left := by
    have hA : (toUnit (pullback b e)).left = (pullback b e).hom := by simpa using Over.w (toUnit (pullback b e))
    rw [← hA]; exact hKl
  have hbfin : IsFinite b.left := by
    have : IsFinite (b.left ≫ B.hom) := by rw [Over.w b]; infer_instance
    exact IsFinite.of_comp b.left B.hom
  have hKfin : IsFinite (pullback b e).hom := by
    have h1 : IsFinite (pullback b e).hom := MorphismProperty.of_isPullback hKl' ‹_›
    exact h1
  have hclosed : IsClosedImmersion (pullback.fst b e).left := by
    have he : IsClosedImmersion e.left := by
      have : IsClosedImmersion (e.left ≫ B.hom) := by
        have : e.left ≫ B.hom = 𝟙 _ := by simpa using Over.w e
        rw [this]; infer_instance
      exact IsClosedImmersion.of_comp _ B.hom
    exact MorphismProperty.of_isPullback hKl'.flip he
  let u : C ⟶ pullback b e := hK.lift a (toUnit C) hab
  have hu1 : u ≫ pullback.fst b e = a := hK.lift_fst _ _ _
  have hu0 : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u) := by
    have hK0 := hK.map (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0))
    have : (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u = (h₀.isoIsPullback _ _ hK0).hom := by
      apply hK0.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp, hu1]
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp, toUnit_unique (u ≫ toUnit _) (toUnit C)]
    rw [this]; infer_instance
  have hu : IsIso u := isIso_of_fibre R C _ u hu0
  refine ⟨?_, hb, surjective_left_of_fibre R A B b hs, ?_⟩
  · have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
    rw [← hu1, Over.comp_left]; infer_instance
  · exact IsPullback.of_iso hK (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hu1]) (by simp) (by simp) (by simp)

theorem exact_of_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B), a ≫ b = toUnit C ≫ e → IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e) → Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  intro R _ _ _ C A B _ _ _ _ _ _ a b e hab h₀ hf hs
  exact main R C A B a b e hab h₀ hf hs

end GlobalTheory.CompanionTheory.Ar.BT.FinFlat
