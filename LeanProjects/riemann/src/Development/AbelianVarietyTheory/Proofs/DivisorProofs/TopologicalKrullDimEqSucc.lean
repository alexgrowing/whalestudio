import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped TensorProduct

namespace GlobalTheory.RegGenSmooth

theorem injective_of_charZero {k A : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CommRing A] [CharZero A] (f : k →+* A) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem smooth_of_regular (K : Type) [Field K] [PerfectField K] (B : Type) [CommRing B]
    [Algebra K B] [Algebra.FiniteType K B] (d : ℕ)
    (h : ∀ (m : Ideal B) [m.IsMaximal], IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = d) :
    SmoothOfRelativeDimension d (spMap (algebraMap K B)) := by
  have : Algebra.FinitePresentation K B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have key (m : Ideal B) (hm : m.IsMaximal) :
      ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f) := by
    obtain ⟨h₁, h₂⟩ := h m
    have h₃ := formallySmooth_of_isRegularLocalRing_of_perfectField K (Localization.AtPrime m)
    have := formallyEtale_residueField_of_isMaximal K K m (Localization.AtPrime m)
    obtain ⟨-, h₄⟩ := free_and_finrank_kaehler_eq_finrank_cotangentSpace K (Localization.AtPrime m)
    have h₅ := (IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime m)).1 h₁
    rw [h₂, ← h₄] at h₅
    have : Algebra.IsSmoothAt K m := h₃
    exact exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt K m (by exact_mod_cast h₅)
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)).mpr ?_
  refine ⟨{f | Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away f)}, ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hs⟩ := key m hm
    exact hf (hle (Ideal.subset_span hs))
  · intro f hf
    have := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).mpr hf
    rwa [IsScalarTower.algebraMap_eq K B] at this

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem ringKrullDim_base (h : IsArithVar p D) : ringKrullDim k = 1 := by
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  rw [ringKrullDim_eq_of_isIntegral ℤ k]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem chart_props (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A] (i : Sp A ⟶ X)
    [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain A ∧ Algebra.FiniteType k A ∧ FaithfulSMul k A := by
  have := h.isDomain
  have := h.finite
  have := h.isIntegral
  have := h.flat
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
  have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have hfl : Flat (i ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h₁ := (flat_int_iff_charZero _).1 hfl
  have : CharZero A := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.toRingHom.charZero_iff
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective |>.1 h₁
  exact ⟨‹_›, RingHom.finiteType_algebraMap.mp hft,
    (faithfulSMul_iff_algebraMap_injective _ _).2 (injective_of_charZero _)⟩

theorem topologicalKrullDim_eq_succ (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {d : ℕ} (hd : topologicalKrullDim Y = d) :
    topologicalKrullDim X = (d + 1 : ℕ) := by
  have := h.isDomain
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hO1 := ringKrullDim_base h
  have hO : ¬ IsField k := fun e => by
    rw [ringKrullDim_eq_zero_of_isField e] at hO1
    exact absurd hO1 (by decide)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
    obtain ⟨_, _, _⟩ := chart_props h i hi
    have h₁ : ringKrullDim (K ⊗[k] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans
      ((IntModel.ringKrullDim_le_add (O := k) K).trans ?_)
    refine (add_le_add hO1.le h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap k K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum k) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem ringKrullDim_chart (h : IsArithVar p D) {K : Type} [Field K] [Algebra k K]
    [IsFractionRing k K] {Y : Scheme.{0}} {j : Y ⟶ X} {q : Y ⟶ Sp K}
    (H : IsPullback j q p (spMap (algebraMap k K))) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    IsDomain (K ⊗[k] A) ∧ ringKrullDim (K ⊗[k] A) = D := by
  have := h.isDomain
  have := h.isIntegral
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  obtain ⟨_, _, _⟩ := chart_props h i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (K ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj : Function.Injective (algebraMap A (K ⊗[k] A)) := IsLocalization.injective _ hle
  refine ⟨this, ?_⟩
  obtain ⟨i₀, _, H₀⟩ := exists_affine_chart_of_isPullback H i hi
  obtain ⟨d, hd, -⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback H inferInstance
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
  let η : Spec (.of (K ⊗[k] A)) := (⟨⊥, inferInstance⟩ : PrimeSpectrum _)
  have e₁ : topologicalKrullDim (closure {i₀ η} : Set Y) = d :=
    (topologicalKrullDim_closure_eq_ringKrullDim_quotient q i₀ η).trans
      ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans hd)
  have e₂ : j (i₀ η) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, H₀.w, Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion i]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  have e₃ : closure {i₀ η} = Set.univ :=
    Set.eq_univ_of_forall fun y => specializes_iff_mem_closure.1
      (j.isEmbedding.isInducing.specializes_iff.1 (e₂ ▸ genericPoint_specializes _))
  rw [e₃, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq] at e₁
  have e₄ := (topologicalKrullDim_eq_succ h H e₁).symm.trans h.dim_eq
  rw [hd]
  have e₅ : d + 1 = D + 1 := by exact_mod_cast e₄
  rw [Nat.succ_injective e₅]

theorem smooth_genericFibre (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    SmoothOfRelativeDimension D (pullback.snd p (spMap (algebraMap k (FractionRing k)))) := by
  have := h.isDomain
  have := h.charZero_base
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  refine smoothOfRelativeDimension_genericFibre_of_affine k X p D fun A _ _ i _ hi => ?_
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have hft : LocallyOfFiniteType (spMap (algebraMap k A)) := by rw [← hi]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp hft
  refine smooth_of_regular _ _ D fun m hm => ⟨?_, ?_⟩
  · obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    have : Flat (spMap (algebraMap k (FractionRing k))) :=
      flat_specMap_localization (nonZeroDivisors k) _
    have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors k)
    let y : Spec (.of (FractionRing k ⊗[k] A)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
    have := GenSpread.isIso_stalkMap_of_flat
      (pullback.fst p (spMap (algebraMap k (FractionRing k)))) (i₀ y)
    have := hr (pullback.fst p (spMap (algebraMap k (FractionRing k))) (i₀ y))
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((pullback.fst p (spMap (algebraMap k (FractionRing k)))).stalkMap (i₀ y)) ≪≫
        asIso (i₀.stalkMap y) ≪≫ Spec.stalkIso (.of _) y).commRingCatIsoToRingEquiv
  · have : Nontrivial (FractionRing k ⊗[k] A) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top |>
      fun _ => (Ideal.Quotient.mk m).domain_nontrivial
    have : Nontrivial A := by
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact false_of_nontrivial_of_subsingleton (FractionRing k ⊗[k] A)
    obtain ⟨_, hd⟩ := ringKrullDim_chart h H i hi
    have e := height_add_ringKrullDim_quotient_of_finiteType (FractionRing k) m
    rw [hd, ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).1 hm),
      add_zero] at e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), e]

theorem exists_opens_smooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x))
    (σ : k →+* ℂ) (y : CxPts p σ) :
    ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension D (U.ι ≫ p) := by
  have := h.isDomain
  have := h.finite
  have := h.isNoetherianRing
  have : IsProper p := CommonModel.isProper_of_isProjOver h.isProjOver
  have : LocallyOfFinitePresentation p := inferInstance
  have := smooth_genericFibre h hr
  have H := IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))
  have : Flat (spMap (algebraMap k (FractionRing k))) :=
    flat_specMap_localization (nonZeroDivisors k) _
  have : IsPreimmersion (spMap (algebraMap k (FractionRing k))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors k)
  obtain ⟨τ, hτ⟩ : ∃ τ : FractionRing k →+* ℂ, τ.comp (algebraMap k _) = σ :=
    ⟨IsFractionRing.lift (K := FractionRing k) (injective_of_charZero σ), RingHom.ext fun a => by
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
  have hτ' : spMap τ ≫ spMap (algebraMap k _) = spMap σ := by
    rw [← hτ, ← Spec.map_comp]
    rfl
  obtain ⟨y', hy'⟩ : ∃ y' : Sp ℂ ⟶ pullback p (spMap (algebraMap k (FractionRing k))),
      y' ≫ pullback.fst _ _ = y.1 :=
    ⟨H.lift y.1 (spMap τ) (y.2.trans hτ'.symm), H.lift_fst _ _ _⟩
  obtain ⟨W, hW, hs⟩ := GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback H D
    (y' (IsLocalRing.closedPoint ℂ))
  refine ⟨W, mem_ptsIn.2 ?_, hs⟩
  change y.1 (IsLocalRing.closedPoint ℂ) ∈ W
  rw [← hy']
  exact hW

theorem genSmooth (h : IsArithVar p D) (hr : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)) :
    GenSmooth p D := fun σ => by
  refine ⟨⟨AlgChart p σ D, id, fun y => ?_⟩⟩
  obtain ⟨W, hW, _⟩ := exists_opens_smooth h hr σ y
  obtain ⟨U, x, hU, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p D W (mem_ptsIn.1 hW)
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

theorem genSmooth_of_isRegSurf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k),
    IsRegSurf p → GenSmooth p 1 ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      ∃ U : X.Opens, y ∈ ptsIn p σ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ p) :=
  fun _ _ _ _ h => ⟨genSmooth h.toIsArithVar h.regular,
    exists_opens_smooth h.toIsArithVar h.regular⟩

end GlobalTheory.RegGenSmooth
