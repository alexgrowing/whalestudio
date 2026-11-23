import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleReducedEq

theorem isRadical_map_of_etale {Q C : Type} [CommRing Q] [CommRing C] [Algebra Q C]
    [Algebra.Etale Q C] (I : Ideal Q) (hI : I.IsRadical) :
    (I.map (algebraMap Q C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have : _root_.IsReduced (TensorProduct Q (Q ⧸ I) C) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Q ⧸ I) _
  have : _root_.IsReduced (TensorProduct Q C (Q ⧸ I)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm Q C (Q ⧸ I)).toRingEquiv (RingEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
    (RingEquiv.injective _)

theorem etale_eval₂Hom_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale) :
    (MvPolynomial.eval₂Hom ψ N).Etale := by
  have : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway g
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have : Algebra.Etale (MvPolynomial ι R) (MvPolynomial ι A) :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R (MvPolynomial ι R) A (MvPolynomial ι A))
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  letI : Algebra (MvPolynomial ι R) C :=
    (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).toAlgebra
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι A) C :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  have : Algebra.Etale (MvPolynomial ι R) C := hE
  exact Algebra.Etale.of_restrictScalars (MvPolynomial ι R) (MvPolynomial ι A) C

theorem isRadical_span_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g δ : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale)
    (hδ : (Ideal.span {algebraMap R A δ}).IsRadical) :
    (Ideal.span {ψ (algebraMap R A δ)}).IsRadical := by
  have he := etale_eval₂Hom_of_away g ψ N hE
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  have : Algebra.Etale (MvPolynomial ι A) C := he
  have hI : (Ideal.map (MvPolynomial.C (σ := ι)) (Ideal.span {algebraMap R A δ})).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced] at hδ ⊢
    exact isReduced_of_injective
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (Ideal.span {algebraMap R A δ})).symm.toRingEquiv
      (RingEquiv.injective _)
  have h2 := isRadical_map_of_etale (C := C) _ hI
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, MvPolynomial.eval₂Hom_C] at h2
  exact h2

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_ger_iff_not_mem {X : Scheme.{0}} (Z : Closeds X) (U' : X.affineOpens)
    (δ : Γ(X, U'.1)) (h : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U' = Ideal.span {δ})
    (x : X) (hx : x ∈ U'.1) : IsUnit (ger x hx δ) ↔ x ∉ Z := by
  obtain ⟨P, rfl⟩ : x ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hx
  have hS : IsClosed (X := PrimeSpectrum Γ(X, U'.1)) (U'.2.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage U'.2.fromSpec.continuous
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at h
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, U'.2.fromSpec_preimage_basicOpen]
  change δ ∉ P.asIdeal ↔ _
  rw [not_iff_not]
  have e := congrArg (P ∈ ·)
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U'.2.fromSpec ⁻¹' (Z : Set X)))
  rw [hS.closure_eq, h, PrimeSpectrum.zeroLocus_span] at e
  have e3 : (δ ∈ P.asIdeal) = (P ∈ PrimeSpectrum.zeroLocus {δ}) :=
    propext ((PrimeSpectrum.mem_zeroLocus (P : PrimeSpectrum Γ(X, U'.1)) {δ}).trans
      Set.singleton_subset_iff).symm
  exact (e3.trans e).to_iff

theorem mem_iff_not_isUnit_ger {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Y, W)) (hP : hW.fromSpec P ∈ W) (c : Γ(Y, W)) :
    c ∈ P.asIdeal ↔ ¬ IsUnit (ger (hW.fromSpec P) hP c) := by
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, hW.fromSpec_preimage_basicOpen]
  change _ ↔ ¬ ¬ c ∈ P.asIdeal
  rw [not_not]

theorem reducedEq_pullback_etale : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  intro X Y _ q ι _ Vo U U' hU' W hW hWU N hEt δ hδ
  have part1 : ∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 →
      (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo) := by
    intro z hz hzU'
    rw [ger_appLE q hWU z hz δ, isUnit_map_iff, ← ger_resG hU' (q z) hzU' δ,
      isUnit_ger_iff_not_mem _ U' _ hδ]
    exact not_not
  refine ⟨part1, ?_⟩
  intro W' hW' hW'U' f hf z hz
  obtain ⟨g, hgU', hzg⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨q z, hW'U' hz⟩ (hWU (hW' hz))
  set g' := resG X hU' g
  set V := X.basicOpen g'
  have hV' : V = X.basicOpen g := by
    simp only [V, g', resG, Scheme.basicOpen_res]
    exact inf_eq_right.2 hgU'
  have hVU' : V ≤ U'.1 := X.basicOpen_le g'
  have hVU : V ≤ U.1 := hVU'.trans hU'
  letI : Algebra Γ(X, U.1) Γ(X, V) := (resG X hVU).toAlgebra
  haveI : IsLocalization.Away g Γ(X, V) := U.2.isLocalization_of_eq_basicOpen g (homOfLE hVU) hV'
  have hδV : (Ideal.span {algebraMap Γ(X, U.1) Γ(X, V) δ}).IsRadical := by
    have e := (Scheme.IdealSheafData.vanishingIdeal Vo.compl).map_ideal_basicOpen U' g'
    rw [hδ, Ideal.map_span, Set.image_singleton] at e
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal
        (X.affineBasicOpen g')).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    rw [← e] at hrad
    have e2 : algebraMap Γ(X, U.1) Γ(X, V) δ =
        (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom (resG X hU' δ) :=
      (resG_resG hU' hVU' δ).symm
    rw [e2]
    exact hrad
  have hzV : q z ∈ V := hV' ▸ hzg
  obtain ⟨h, hhle, hzh⟩ := hW.exists_basicOpen_le (V := W' ⊓ q ⁻¹ᵁ V) ⟨z, hz, hzV⟩ (hW' hz)
  set W1 := Y.basicOpen h
  have hW1W : W1 ≤ W := Y.basicOpen_le h
  have hW1V : W1 ≤ q ⁻¹ᵁ V := hhle.trans inf_le_right
  have hW1W' : W1 ≤ W' := hhle.trans inf_le_left
  have hW1 : IsAffineOpen W1 := hW.basicOpen h
  let ψ : Γ(X, V) →+* Γ(Y, W1) := (q.appLE V W1 hW1V).hom
  have hcomp : MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i)) =
      (resG Y hW1W).comp (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra, ψ, resG]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
    · intro i
      simp
  have hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i))).Etale := by
    rw [hcomp]
    have h2 : (resG Y hW1W).Etale := by
      letI : Algebra Γ(Y, W) Γ(Y, W1) := (resG Y hW1W).toAlgebra
      haveI : IsLocalization.Away h Γ(Y, W1) := hW.isLocalization_basicOpen h
      exact Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ hEt h2
  have rad := isRadical_span_of_away g δ ψ (fun i => resG Y hW1W (N i)) hE hδV
  have hd : ψ (algebraMap Γ(X, U.1) Γ(X, V) δ) = resG Y hW1W ((q.appLE U.1 W hWU).hom δ) := by
    have := congrArg (fun F => F (MvPolynomial.C δ)) hcomp
    simpa using this
  set d := ψ (algebraMap Γ(X, U.1) Γ(X, V) δ)
  set b := resG Y hW1W' f
  have hb : b ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hdP, hP⟩
    let P' : Spec Γ(Y, W1) := ⟨P, hP⟩
    have hz' : hW1.fromSpec P' ∈ W1 := by
      rw [← SetLike.mem_coe, ← hW1.range_fromSpec]; exact Set.mem_range_self _
    have hdP' : d ∈ P'.asIdeal := hdP (Ideal.mem_span_singleton_self d)
    rw [mem_iff_not_isUnit_ger hW1 P' hz', hd, ger_resG] at hdP'
    have hq : q (hW1.fromSpec P') ∉ Vo := by
      rw [← part1 _ (hW1W hz') (hVU' (hW1V hz'))]
      exact hdP'
    have hm := hf _ (hW1W' hz') hq
    change b ∈ P'.asIdeal
    rw [mem_iff_not_isUnit_ger hW1 P' hz', ger_resG]
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (rad hb)
  refine ⟨ger z hzh c, ?_⟩
  rw [← ger_resG hW1W' z hzh f, ← ger_resG hW1W z hzh, ← hd]
  change ger z hzh b = _
  rw [← hc, map_mul, mul_comm]

end GlobalTheory.EtaleReducedEq
