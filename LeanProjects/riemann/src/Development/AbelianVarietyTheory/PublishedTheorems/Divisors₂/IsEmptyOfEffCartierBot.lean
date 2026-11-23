import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.Principalise.Model

attribute [local instance] MvPolynomial.gradedAlgebra

def Concl {k : Type} [Field k] (d : ℕ) {Y : Scheme.{0}} (f : Y ⟶ Sp k) (I : Y.IdealSheafData) : Prop :=
  ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
    IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
    IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
    FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)

theorem regular_stalk {k : Type} [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k) [Smooth f] (y : Y) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hs : (f.appLE ⊤ U (by simp)).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have hk : IsField Γ(Sp k, ⊤) :=
    MulEquiv.isField (Field.toIsField k) (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  let := hk.toField
  let := (f.appLE ⊤ U (by simp)).hom.toAlgebra
  have : Algebra.Smooth Γ(Sp k, ⊤) Γ(Y, U) := hs
  have hr : IsRegularRing Γ(Y, U) := isRegularRing_of_smooth Γ(Sp k, ⊤) Γ(Y, U)
  let := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  have := hU.isLocalization_stalk ⟨y, hy⟩
  have h := isRegularRing_iff.mp hr (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨y, hy⟩).asIdeal) (Y.presheaf.stalk y)).toRingEquiv

theorem concl_top {k : Type} [Field k] (d : ℕ) {Y : Scheme.{0}} (f : Y ⟶ Sp k) (h₁ : IsIntegral Y)
    (h₂ : SmoothOfRelativeDimension d f) (h₃ : IsProjOver f) : Concl d f ⊤ := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  refine ⟨Y, 𝟙 Y, h₁, by simpa using h₂, by simpa using h₃, .id, inferInstance, ?_, fun y => ?_⟩
  · rw [Scheme.IdealSheafData.comap_id]; exact effCartier_top Y
  · exact sncAt_of_not_mem _ y (by simp) (regular_stalk f y)

theorem isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, f, hx, hf, e⟩ := h x
  have hf0 : f = 0 := by
    have : f ∈ (⊥ : W.IdealSheafData).ideal U := e ▸ Ideal.mem_span_singleton_self f
    simpa using this
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  exact nonZeroDivisors.ne_zero hf hf0

theorem not_concl_bot {k : Type} [Field k] (d : ℕ) {Y : Scheme.{0}} (f : Y ⟶ Sp k) : ¬ Concl d f ⊥ := by
  rintro ⟨Y', s, h, -, -, -, -, hE, -⟩
  rw [Scheme.IdealSheafData.comap_bot] at hE
  exact (isEmpty_of_effCartier_bot hE).false (Nonempty.some inferInstance)

theorem blowup_bot (X : Scheme.{0}) : FinalTheorems.Blowup (Scheme.emptyTo X) ⊥ := by
  refine ⟨fun x => isEmptyElim x, fun W g hg => ?_⟩
  rw [Scheme.IdealSheafData.comap_bot] at hg
  have := isEmpty_of_effCartier_bot hg
  have hW := isInitialOfIsEmpty (X := W)
  exact ⟨hW.to _, hW.hom_ext _ _, fun _ _ => hW.hom_ext _ _⟩

theorem seq_empty {S Y : Scheme.{0}} (f : Y ⟶ S) [Smooth f] : IsSmoothBlowupSeq f Set.univ (Scheme.emptyTo Y) :=
  .single ⊥ _ inferInstance (Set.subset_univ _) (blowup_bot Y)

theorem isIso_of_seq_empty {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {s : Y' ⟶ Y} (h : IsSmoothBlowupSeq f ∅ s) :
    IsIso (s ∣_ ⊤) := h.isIso_restrict ⊤ (by simp)

section Proj
variable (k : Type) [Field k] (N : ℕ)

def hypPt : PSpace k (N + 1) :=
  (⟨⟨Ideal.span {MvPolynomial.X 0}, Ideal.homogeneous_span _ _ (by
      rintro _ rfl; exact ⟨1, MvPolynomial.isHomogeneous_X k 0⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).2 MvPolynomial.X_prime, fun h => by
      have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin (N + 1 + 1)) k) ∈
          HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) one_pos (MvPolynomial.isHomogeneous_X k 1)
      have h2 := Ideal.mem_span_singleton.1 (h h1)
      rw [MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by simp)⟩ : ProjectiveSpectrum _)

def hypPt' : PSpace k (N + 1) :=
  (⟨⟨Ideal.span {MvPolynomial.X 1}, Ideal.homogeneous_span _ _ (by
      rintro _ rfl; exact ⟨1, MvPolynomial.isHomogeneous_X k 1⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 1)).2 MvPolynomial.X_prime, fun h => by
      have h1 : (MvPolynomial.X 0 : MvPolynomial (Fin (N + 1 + 1)) k) ∈
          HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) one_pos (MvPolynomial.isHomogeneous_X k 0)
      have h2 := Ideal.mem_span_singleton.1 (h h1)
      rw [MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by simp)⟩ : ProjectiveSpectrum _)

def hypIdeal : (PSpace k (N + 1)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Opens.compl (Proj.basicOpen _ (MvPolynomial.X 0)))

theorem mem_support : hypPt k N ∈ (hypIdeal k N).support := by
  rw [hypIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact fun h => (Proj.mem_basicOpen _ _ _).1 h (Ideal.mem_span_singleton_self _)

theorem not_mem_support : hypPt' k N ∉ (hypIdeal k N).support := by
  rw [hypIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine fun h => h ((Proj.mem_basicOpen _ _ _).2 fun h1 => ?_)
  have h2 := Ideal.mem_span_singleton.1 h1
  rw [MvPolynomial.X_dvd_X] at h2
  exact absurd h2 (by simp)

theorem hyp_proj : IsIntegral (PSpace k (N + 1)) ∧ SmoothOfRelativeDimension (N + 1) (PSpace.str k (N + 1)) ∧
    IsProjOver (PSpace.str k (N + 1)) ∧ hypIdeal k N ≠ ⊥ ∧ hypIdeal k N ≠ ⊤ := by
  refine ⟨inferInstance, Adelic.smoothOfRelativeDimension_pspace k _, ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩,
    fun e => not_mem_support k N ?_, fun e => ?_⟩
  · rw [e, Scheme.IdealSheafData.support_bot]; trivial
  · have := mem_support k N
    rw [e, Scheme.IdealSheafData.support_top] at this; exact this

theorem concl_proj [CharZero k] (h : Published.Principalisation) :
    Concl (N + 1) (PSpace.str k (N + 1)) (hypIdeal k N) :=
  h k _ _ _ (hyp_proj k N).1 (hyp_proj k N).2.1 (hyp_proj k N).2.2.1 _ (hyp_proj k N).2.2.2.1

end Proj

section Line
variable (k : Type) [Field k]

abbrev origin : Sp k ⟶ Sp (Polynomial k) := spMap (Polynomial.evalRingHom 0)

instance : IsClosedImmersion (origin k) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩

theorem effCartier_origin : FinalTheorems.EffCartier (origin k).ker := fun x => by
  let e := (Scheme.ΓSpecIso (.of (Polynomial k))).commRingCatIsoToRingEquiv
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm Polynomial.X, trivial, ?_, ?_⟩
  · exact mem_nonZeroDivisors_of_ne_zero (by simp)
  · rw [Scheme.Hom.ker_apply]
    ext a
    obtain ⟨p, rfl⟩ := e.symm.surjective a
    have h := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) p
    have h' : (origin k).appTop (e.symm p) = (Scheme.ΓSpecIso (.of k)).inv (p.eval 0) := h.symm
    rw [Ideal.mem_span_singleton, map_dvd_iff, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero,
      RingHom.mem_ker]
    refine Iff.trans (by rw [← h']; rfl) (map_eq_zero_iff (Scheme.ΓSpecIso (.of k)).inv.hom
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.injective)

theorem smooth_origin : Smooth ((origin k).ker.subschemeι ≫ spMap (Polynomial.C : k →+* Polynomial k)) := by
  have e : origin k ≫ spMap (Polynomial.C : k →+* Polynomial k) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1; ext; simp
  have e' : (origin k).ker.subschemeι ≫ spMap (Polynomial.C : k →+* Polynomial k) = inv (origin k).toImage := by
    rw [← cancel_epi (origin k).toImage, ← Category.assoc, IsIso.hom_inv_id, ← e]
    congr 1
    exact (origin k).toImage_imageι
  rw [e']; infer_instance

theorem step_origin : Smooth ((origin k).ker.subschemeι ≫ spMap (Polynomial.C : k →+* Polynomial k)) ∧
    ((origin k).ker.support : Set (Sp (Polynomial k))).Nonempty ∧ FinalTheorems.Blowup (𝟙 _) (origin k).ker :=
  ⟨smooth_origin k, ⟨origin k (Nonempty.some inferInstance),
    (origin k).range_subset_ker_support ⟨_, rfl⟩⟩, blowup_id (effCartier_origin k)⟩

end Line

end GlobalTheory.Principalise.Model
