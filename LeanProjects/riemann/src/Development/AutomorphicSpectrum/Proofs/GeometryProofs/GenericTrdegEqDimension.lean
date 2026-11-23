import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptTrdeg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem trdeg_residueField_of_isIntegral {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B]
    [Algebra.IsIntegral K B] (q : Ideal B) [q.IsPrime] :
    Algebra.trdeg ℤ q.ResidueField = Algebra.trdeg ℤ K := by
  have hcm : (Ideal.comap (algebraMap K B) q).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := K) q hcm
  have hs : Function.Surjective (IsScalarTower.toAlgHom K B q.ResidueField) :=
    Ideal.algebraMap_residueField_surjective q
  have : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_surjective _ hs
  have : CharZero q.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K q.ResidueField).injective
  have h0 : Algebra.trdeg K q.ResidueField = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq ℤ K (A := q.ResidueField), h0, add_zero]

theorem trdeg_int_eq_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (e : A ≃+* B) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ B :=
  (AlgEquiv.ofRingEquiv (f := e) (fun n => by simp [eq_intCast (algebraMap ℤ A), eq_intCast (algebraMap ℤ B)])).trdeg_eq

theorem residueFieldMap_bijective {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun b => ?_⟩
  obtain ⟨c, rfl⟩ := X.residue_surjective x b
  obtain ⟨d, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective f x c
  exact ⟨Y.residue (f x) d, congr($(Scheme.residue_residueFieldMap f x).hom d)⟩

theorem trdeg_residueField_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hγ : Function.Injective g₀)
    (hF : letI := β.toAlgebra; ∀ u : F, ∃ a : O, a ≠ 0 ∧ _root_.IsIntegral O (a • u))
    {y : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) :
    Algebra.trdeg ℤ ((pullback s (spMap β)).residueField y) = Algebra.trdeg ℤ Ω₀ := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  obtain ⟨z, rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := HodgeBasic.isIntegral_tensor hγ hF
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have h1 : Algebra.trdeg ℤ p.asIdeal.ResidueField = Algebra.trdeg ℤ Ω₀ :=
    trdeg_residueField_of_isIntegral (K := Ω₀) p.asIdeal
  have hst : SurjectiveOnStalks (pullback.fst (pullback.fst s (spMap β)) ξ₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip hsurj
  have h2 := trdeg_int_eq_of_ringEquiv (RingEquiv.ofBijective _ (residueFieldMap_bijective
    (pullback.fst (pullback.fst s (spMap β)) ξ₀) z))
  have h3 := trdeg_int_eq_of_ringEquiv (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have h4 : Algebra.trdeg ℤ ((Spec (.of (Ω₀ ⊗[O] F))).residueField p) = Algebra.trdeg ℤ p.asIdeal.ResidueField :=
    trdeg_int_eq_of_ringEquiv (B := p.asIdeal.ResidueField)
      (Scheme.Spec.residueFieldIso (.of (Ω₀ ⊗[O] F)) p).commRingCatIsoToRingEquiv
  exact h2.trans (h3.symm.trans (h4.trans h1))

theorem trdeg_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Function.Injective β → IsCptGen ξ₀ → x ≫ Y.j = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ → Algebra.trdeg ℤ Ω₀ = ((D.dim : ℕ) : Cardinal) := by
  intro E _ _ _ H D l Xo c O _ β Y Ω₀ _ ξ₀ Ω _ x i hβ h₀ hx
  have := c.fin
  have := Y.jQ_open

  let g₀ : O →+* Ω₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hs : ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let str := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let cst : c.F →+* Ω := (Spec.preimage (x ≫ str)).hom
  have hc : x ≫ str = spMap cst := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ str)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hj : Y.j ≫ Y.s = str ≫ spMap β := by
    simp only [Model.j, Category.assoc, pullback.condition]
    rw [← Category.assoc, Y.jQ_over]
  have hcomp : i.comp g₀ = cst.comp β := by
    have h1 : spMap (i.comp g₀) = spMap (cst.comp β) := by
      have h2 : spMap i ≫ ξ₀ ≫ Y.s = x ≫ str ≫ spMap β := by
        rw [← hj, ← Category.assoc, ← Category.assoc, ← hx]
      rw [hs, ← Category.assoc, hc] at h2
      simpa only [spMap, CommRingCat.ofHom_comp, Spec.map_comp] using h2
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have hg : Function.Injective g₀ := by
    refine Function.Injective.of_comp (f := i) ?_
    have h3 : (i ∘ g₀) = cst ∘ β := congrArg DFunLike.coe hcomp
    rw [h3]
    exact cst.injective.comp hβ
  have hΩ : CharZero Ω := charZero_of_injective_ringHom cst.injective
  have hΩ₀ : CharZero Ω₀ := (RingHom.charZero_iff i.injective).2 hΩ

  let w : Xo.XF c := x (IsLocalRing.closedPoint Ω)
  have hy : pullback.fst Y.s (spMap β) (Y.jQ w) = genPt ξ₀ := by
    have h4 : pullback.fst Y.s (spMap β) (Y.jQ w) = (x ≫ Y.j) (IsLocalRing.closedPoint Ω) := rfl
    have h6 : (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) (IsLocalRing.closedPoint Ω) =
        ξ₀ ((Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω)) := rfl
    have h5 : (Spec.map (CommRingCat.ofHom i)) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint Ω₀ :=
      Subsingleton.elim (α := PrimeSpectrum _) _ _
    rw [h4, hx, h6, h5]
    rfl
  have hF := HodgeBasic.exists_integral_multiple_of_injective β hβ
  have hw : ∀ w' : Xo.XF c, w' ⤳ w → w' = w := fun w' h =>
    Y.jQ.isOpenEmbedding.injective
      (HodgeBasic.eq_of_specializes_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy (h.map Y.jQ.continuous))

  have hsm : SmoothOfRelativeDimension D.dim str :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  obtain ⟨-, htr⟩ := GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension str D.dim hsm w hw
  letI : Algebra c.F ((Xo.XF c).residueField w) :=
    (Spec.preimage ((Xo.XF c).fromSpecResidueField w ≫ str)).hom.toAlgebra
  have : CharZero ((Xo.XF c).residueField w) :=
    charZero_of_injective_algebraMap (algebraMap c.F ((Xo.XF c).residueField w)).injective
  have h6 : Algebra.trdeg ℤ ((Xo.XF c).residueField w) = (D.dim : Cardinal) := by
    have hal : Algebra.IsAlgebraic ℤ c.F :=
      ⟨fun u => (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)⟩
    have h0 : Algebra.trdeg ℤ c.F = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℤ c.F (A := (Xo.XF c).residueField w), h0, zero_add]
    exact htr
  have h7 := trdeg_int_eq_of_ringEquiv (asIso (Y.jQ.residueFieldMap w)).commRingCatIsoToRingEquiv
  have h8 := trdeg_residueField_of_fst Y.s β g₀ ξ₀ h₀ hs hg hF hy
  rw [← h8, h7, h6]

end GlobalTheory.CompanionTheory.Ar.CptTrdeg
