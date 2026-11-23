import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FormallySmoothQuotient
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.HenselZero

theorem exists_factor_stalk {X : Scheme.{0}} {T : CommRingCat.{0}} [IsLocalRing T] (w : Spec T ⟶ X) {y : X}
    (hw : w (closedPoint T) = y) : ∃ χ : X.presheaf.stalk y ⟶ T, Spec.map χ ≫ X.fromSpecStalk y = w := by
  subst hw
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk w⟩

theorem exists_formallySmooth_stalk {O : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec O) [Smooth p] (y : X) :
    ∃ α : O ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ p := by
  let τ : O ⟶ (Spec O).presheaf.stalk (p y) := StructureSheaf.toStalk O (p y)
  refine ⟨τ ≫ p.stalkMap y, ?_, ?_⟩
  · have hs : (p.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (p.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra O ((Spec O).presheaf.stalk (p y)) := StructureSheaf.stalkAlgebra O (p y)
    have := (p y).isPrime
    have : IsLocalization.AtPrime ((Spec O).presheaf.stalk (p y)) (p y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk O (p y)
    have h₀ : Algebra.FormallySmooth O ((Spec O).presheaf.stalk (p y)) :=
      Algebra.FormallySmooth.of_isLocalization (p y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec O).fromSpecStalk (p y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]

theorem fromSpecStalk_mem_basicOpen {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk y)) (hq : (X.presheaf.germ U y hy).hom f ∉ q.asIdeal) :
    X.fromSpecStalk y q ∈ X.basicOpen f := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hy]
  simp only [CommRingCat.comp_apply]
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  exact ⟨ht trivial, hq⟩

section Fibre

variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ

theorem isClosedImmersion_fibre : IsClosedImmersion φ :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hφ.flip
    (IsClosedImmersion.spec_of_surjective _ residue_surjective)

theorem maximalIdeal_le_span_sup {ι : Type} (y : Y) (α : CommRingCat.of O ⟶ X.presheaf.stalk (φ y))
    (hα : Spec.map α = X.fromSpecStalk (φ y) ≫ p) (f : ι → X.presheaf.stalk (φ y))
    (h : maximalIdeal _ ≤ Ideal.span (Set.range fun i => (φ.stalkMap y).hom (f i))) :
    maximalIdeal _ ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map α.hom := by
  have := isClosedImmersion_fibre hφ
  let I := (maximalIdeal O).map α.hom
  by_cases hI : I = ⊤
  · exact le_sup_of_le_right (le_top.trans hI.ge)
  have : Nontrivial (X.presheaf.stalk (φ y) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (X.presheaf.stalk (φ y) ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  let π : X.presheaf.stalk (φ y) ⟶ .of (X.presheaf.stalk (φ y) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let β : ResidueField O →+* X.presheaf.stalk (φ y) ⧸ I := Ideal.quotientMap I α.hom Ideal.le_comap_map
  have hw : (Spec.map π ≫ X.fromSpecStalk (φ y)) ≫ p = spMap β ≫ spMap (residue O) := by
    rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨χ, hχ⟩ := exists_factor_stalk (hφ.lift _ _ hw) (y := y) (φ.isClosedEmbedding.injective (by
    refine (congrArg (fun g => g (closedPoint (X.presheaf.stalk (φ y) ⧸ I))) (hφ.lift_fst _ _ hw)).trans ?_
    exact (congrArg (X.fromSpecStalk (φ y)) (comap_closedPoint (Ideal.Quotient.mk I))).trans
      Scheme.fromSpecStalk_closedPoint))
  have e : φ.stalkMap y ≫ χ = π := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ y)), Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      reassoc_of% hχ, hφ.lift_fst]
  have e' : ∀ a, χ.hom ((φ.stalkMap y).hom a) = Ideal.Quotient.mk I a := fun a => congrArg (fun g => g.hom a) e
  intro a ha
  obtain hr := Ideal.mem_map_of_mem χ.hom (h (map_nonunit (φ.stalkMap y).hom a ha))
  rw [e', Ideal.map_span, ← Set.range_comp] at hr
  have hr' : Ideal.Quotient.mk I a ∈ (Ideal.span (Set.range f)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact (congrArg (fun F => _ ∈ Ideal.span (Set.range F)) (funext fun i => e' (f i))).mp hr
  exact Ideal.mem_quotient_iff_mem_sup.1 hr'

end Fibre

theorem exists_section_of_transversal {O ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Fintype ι] [DecidableEq ι] {X Y : Scheme.{0}} {p : X ⟶ Sp O} [Smooth p]
    {q : Y ⟶ Sp (ResidueField O)} {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
    (t : Sp (ResidueField O) ⟶ Y) (ht : t ≫ q = 𝟙 _) (pt : Sp (ResidueField O)) {U : X.Opens} (hU : φ (t pt) ∈ U)
    (f : ι → Γ(X, U)) (hf : ∀ i, valT (t ≫ φ) U (f i) = 0)
    (hm : maximalIdeal _ ≤ Ideal.span (Set.range fun i => gs φ (t pt) U (f i)))
    (w : ι → (Sp (DualNumber (ResidueField O)) ⟶ Y))
    (hw₁ : ∀ k, spMap (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom ≫ w k = t)
    (hw₂ : ∀ k, w k ≫ q = spMap (algebraMap _ _))
    (hd : (Matrix.of fun i k => (valT (w k ≫ φ) U (f i)).snd).det ≠ 0) :
    ∃ z : Sp O ⟶ X, z ≫ p = 𝟙 _ ∧ spMap (residue O) ≫ z = t ≫ φ ∧ (∀ i, valT z U (f i) = 0) ∧
      ∀ y, y ⤳ φ (t pt) → (∀ i, y ∉ X.basicOpen (f i)) → ∃ r, z r = y := by
  obtain rfl : pt = closedPoint (ResidueField O) := Subsingleton.elim (α := PrimeSpectrum (ResidueField O)) _ _
  set y₀ := φ (t (closedPoint (ResidueField O))) with hy₀
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨α, hs, hα⟩ := exists_formallySmooth_stalk p y₀
  obtain ⟨u, hu⟩ := exists_factor_stalk (t ≫ φ) (y := y₀) rfl
  have : IsLocalRing (DualNumber (ResidueField O)) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _
  have hχ := fun k => exists_factor_stalk (w k ≫ φ) (y := y₀) (by
    have h1 : IsLocalHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
    rw [← comap_closedPoint (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom,
      hy₀, ← hw₁ k]
    rfl)
  choose χ hχ using hχ
  letI := α.hom.toAlgebra
  have : Algebra.FormallySmooth O (X.presheaf.stalk y₀) := hs
  have e₁ : α ≫ u = CommRingCat.ofHom (residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hu, hφ.w, reassoc_of% ht]
  have e₂ : ∀ k, χ k ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom = u := fun k => by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk y₀), Spec.map_comp, Category.assoc, hχ, hu, ← hw₁ k, Category.assoc]
  have e₃ : ∀ k, α ≫ χ k = CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom (algebraMap _ _) := fun k => by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ, hφ.w, reassoc_of% hw₂, Spec.map_comp]
  obtain ⟨ψ, hψ, hk⟩ := exists_algHom_ker_eq (O := O) (fun i => (X.presheaf.germ U y₀ hU).hom (f i)) u.hom
    (fun r => congrArg (fun g => g.hom r) e₁)
    (fun i => (JacGen.valT_specMap_fromSpecStalk hU u (f i)).symm.trans (hu ▸ hf i))
    (fun k => (χ k).hom) (fun k a => congrArg (fun g => g.hom a) (e₂ k))
    (fun k r => congrArg (fun g => g.hom r) (e₃ k))
    (by
      refine fun h => hd (Eq.trans ?_ h)
      congr 1
      ext i k
      rw [Matrix.of_apply, Matrix.of_apply, ← hχ, JacGen.valT_specMap_fromSpecStalk hU])
    (maximalIdeal_le_span_sup hφ _ α hα _ (hm.trans_eq (congrArg (fun F => Ideal.span (Set.range F))
      (funext fun i => (gs_eq φ _ U hU _).trans (Scheme.Hom.germ_stalkMap_apply φ U _ hU _).symm))))
  have hs' : Function.Surjective ψ := fun r => ⟨_, ψ.commutes r⟩
  refine ⟨spMap ψ.toRingHom ≫ X.fromSpecStalk y₀, ?_, ?_, fun i => ?_, fun y hy hyf => ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact ψ.commutes r
  · rw [← hu, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hψ a
  · exact (JacGen.valT_specMap_fromSpecStalk hU (CommRingCat.ofHom ψ.toRingHom) (f i)).trans
      (hk.ge (Ideal.subset_span ⟨i, rfl⟩))
  · obtain ⟨r, rfl⟩ : y ∈ Set.range (X.fromSpecStalk y₀) := by
      rw [Scheme.range_fromSpecStalk]
      exact hy
    obtain ⟨r', hr'⟩ : r ∈ Set.range (PrimeSpectrum.comap ψ.toRingHom) := by
      rw [range_comap_of_surjective _ _ hs']
      refine hk.le.trans (Ideal.span_le.2 ?_)
      rintro _ ⟨i, rfl⟩
      by_contra hn
      exact hyf i (fromSpecStalk_mem_basicOpen hU _ r hn)
    exact ⟨r', congrArg (X.fromSpecStalk y₀) hr'⟩

end GlobalTheory.HenselZero
end
