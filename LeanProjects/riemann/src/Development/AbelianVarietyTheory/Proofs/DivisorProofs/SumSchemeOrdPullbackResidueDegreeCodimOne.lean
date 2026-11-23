import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericallyFiniteFiniteNearCodimOnePointStatement
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypC
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaDegBotEqFinrankFiniteDomainStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.OrdPull

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  let e' : A ≃ₐ[A] B := { e with commutes' := fun _ => rfl }
  unfold Ring.ord
  rw [← Module.length_eq_of_surjective (S := A) (R := B) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) e'
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq.symm

theorem ord_isLocalization {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization.AtPrime A p] (a : R) :
    Ring.ord A (algebraMap R A a) = Ring.ord (Localization.AtPrime p) (algebraMap R _ a) := by
  rw [← ord_ringEquiv (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv]
  exact congrArg _ ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).commutes a).symm

theorem inertiaDeg_isLocalization {R : Type} [CommRing R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization M A] (Q : Ideal A) [Q.IsPrime] : Q.inertiaDeg R = 1 := by
  letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
  rw [Ideal.inertiaDeg_def]
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime Q) Q
  have hs : Function.Surjective (algebraMap (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)) := by
    have h := (IsLocalization.algEquiv (Q.under R).primeCompl (Localization.AtPrime (Q.under R))
      (Localization.AtPrime Q)).surjective
    convert h using 1
    funext x
    refine RingHom.congr_fun (f := algebraMap _ _) (g := (IsLocalization.algEquiv (Q.under R).primeCompl (Localization.AtPrime (Q.under R))
      (Localization.AtPrime Q)).toRingEquiv.toRingHom) (IsLocalization.ringHom_ext (Q.under R).primeCompl ?_) x
    ext r
    simp [← IsScalarTower.algebraMap_apply]
  refine Module.finrank_of_bijective_algebraMap ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨IsLocalRing.residue _ x, rfl⟩

theorem ord_germ_eq (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens) [Nonempty V]
    (hV : IsAffineOpen V) (z : X) (hz : z ∈ V) (h1 : Order.coheight z = 1) (a : Γ(X, V)) (ha : a ≠ 0) :
    Scheme.ord (X.germToFunctionField V a) z =
      ((Ring.ord (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) (algebraMap Γ(X, V) _ a)).toNat : ℤ) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hz⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz a,
    ord_algebraMap h1 ((map_ne_zero_iff _ (germ_injective_of_isIntegral X z hz)).2 ha),
    ← ord_isLocalization _ (X.presheaf.stalk z)]
  rfl

theorem residueDegree_genericPoint_eq_finrank (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X)
    (V : X.Opens) [Nonempty V] [Nonempty (g ⁻¹ᵁ V)] (hV : IsAffineOpen V) (hU : IsAffineOpen (g ⁻¹ᵁ V))
    (hf : (g.app V).hom.Finite) (hi : Function.Injective (g.app V).hom) :
    letI : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
    g.residueDegree (genericPoint Y) = Module.finrank Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := by
  letI : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  haveI : Module.Finite Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := hf
  have h2 : genericPoint Y ∈ g ⁻¹ᵁ V := gen_mem (Classical.arbitrary (g ⁻¹ᵁ V)).2
  rw [GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart X Y g V hV hU _ h2, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  exact GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain _ _ hi

theorem sum_ord_inertiaDeg (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] (hi : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime]
    (hp : p.height = 1) (a : R) (ha : a ≠ 0) :
    ∑ᶠ q ∈ {q : PrimeSpectrum S | q.asIdeal.comap (algebraMap R S) = p},
      ((Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap S _ (algebraMap R S a))).toNat : ℤ) *
        (q.asIdeal.inertiaDeg R : ℤ) =
      (Module.finrank R S : ℤ) * ((Ring.ord (Localization.AtPrime p) (algebraMap R _ a)).toNat : ℤ) := by
  let A := Localization.AtPrime p
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  let B := Localization M
  have hM : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hi).2 fun h => hr (h ▸ p.zero_mem))
  haveI : IsDomain B := IsLocalization.isDomain_localization hM
  haveI : Module.Finite A B := Module.Finite.of_isLocalization R S p.primeCompl
  have hiAB : Function.Injective (algebraMap A B) := localizationAlgebra_injective A B hi
  have hd : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A, hp]; rfl
  have haA : algebraMap R A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors)).2 ha
  have hr : Module.finrank A B = Module.finrank R S := by
    rw [IsLocalization.finrank_eq A p.primeCompl p.primeCompl_le_nonZeroDivisors]
    exact IsLocalizedModule.finrank_eq p.primeCompl (IsScalarTower.toAlgHom R S B).toLinearMap
      p.primeCompl_le_nonZeroDivisors
  rw [← hr, ← GlobalTheory.T.finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord' A B hiAB hd _ haA]
  have hc : ∀ Q : Ideal B, (Q.comap (algebraMap S B)).comap (algebraMap R S) =
      (Q.comap (algebraMap A B)).comap (algebraMap R A) := fun Q => by
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  symm
  refine finsum_mem_eq_of_bijOn (PrimeSpectrum.comap (algebraMap S B)) ⟨?_, ?_, ?_⟩ ?_
  · intro Q hQ
    change (Q.asIdeal.comap (algebraMap S B)).comap (algebraMap R S) = p
    rw [hc, show Q.asIdeal.comap (algebraMap A B) = _ from hQ]
    exact Localization.AtPrime.under_maximalIdeal
  · exact (PrimeSpectrum.localization_comap_injective B M).injOn
  · intro q hq
    have hq' : q.asIdeal.comap (algebraMap R S) = p := hq
    have : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S B)) := by
      rw [PrimeSpectrum.localization_comap_range B M]
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨r, hr, rfl⟩ h
      exact hr (hq' ▸ h)
    obtain ⟨Q, rfl⟩ := this
    refine ⟨Q, ?_, rfl⟩
    change Q.asIdeal.comap (algebraMap A B) = _
    refine (IsLocalization.orderEmbedding p.primeCompl A).injective ?_
    exact (hc _).symm.trans (hq'.trans Localization.AtPrime.under_maximalIdeal.symm)
  · intro Q hQ
    haveI : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal) (Q.asIdeal.under S) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ Q.asIdeal
    have e1 := ord_isLocalization (Q.asIdeal.under S) (Localization.AtPrime Q.asIdeal) (algebraMap R S a)
    have e2 : algebraMap B (Localization.AtPrime Q.asIdeal) (algebraMap A B (algebraMap R A a)) =
        algebraMap S _ (algebraMap R S a) := by
      rw [← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B,
        ← IsScalarTower.algebraMap_apply S B]
    have e3 := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under S) Q.asIdeal
    have e4 := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under A) Q.asIdeal
    rw [inertiaDeg_isLocalization M B, mul_one] at e3
    rw [inertiaDeg_isLocalization p.primeCompl A, one_mul] at e4
    rw [e2, e1, ← e4, e3]
    rfl

theorem comap_primeIdealOf {X Y : Scheme.{0}} (g : Y ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V) :
    (hU.primeIdealOf ⟨w, hw⟩).asIdeal.comap (g.app V).hom = (hV.primeIdealOf ⟨g w, hw⟩).asIdeal := by
  ext s
  rw [Ideal.mem_comap, ← ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf hU w hw,
    ← ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf hV (g w) hw]
  have e := Scheme.evaluation_naturality_apply g w hw s
  have h := map_eq_zero_iff (g.residueFieldMap w).hom (g.residueFieldMap w).hom.injective
    (x := X.evaluation V (g w) hw s)
  rw [e] at h
  exact h

theorem finite_app {X Y : Scheme.{0}} (g : Y ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    [IsFinite (g ∣_ V)] : IsAffineOpen (g ⁻¹ᵁ V) ∧ (g.app V).hom.Finite := by
  haveI : IsAffine V := hV
  refine ⟨isAffine_of_isAffineHom (g ∣_ V), ?_⟩
  have h1 := IsFinite.finite_app (g ∣_ V) ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h1
  have h2 : (g.app (V.ι ''ᵁ ⊤)).hom.Finite := (RingHom.finite_respectsIso.cancel_right_isIso _ _).1 h1
  rwa [V.ι_image_top] at h2

theorem height_primeIdealOf {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (z : X) (hz : z ∈ V)
    (h : Order.coheight z = 1) : (hV.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
  rw [idealHeight_eq_coheight Γ(X, V) (hV.primeIdealOf ⟨z, hz⟩),
    ← coheight_eq_of_isOpenImmersion (x := hV.primeIdealOf ⟨z, hz⟩) hV.fromSpec]
  have h₃ : hV.fromSpec.base (hV.primeIdealOf ⟨z, hz⟩) = z := hV.fromSpec_primeIdealOf ⟨z, hz⟩
  rw [h₃, h]

theorem ord_div {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {u v : X.functionField}
    (hu : u ≠ 0) (hv : v ≠ 0) (x : X) : Scheme.ord (u / v) x = Scheme.ord u x - Scheme.ord v x := by
  have e := Scheme.ord_mul (x := x) (div_ne_zero hu hv) hv
  rw [div_mul_cancel₀ u hv] at e
  omega

theorem fnMap_germ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X)
    (hsp : g (genericPoint Y) ⤳ genericPoint X) (V : X.Opens) [Nonempty V] [Nonempty (g ⁻¹ᵁ V)] (a : Γ(X, V)) :
    TrueGeo.SmallSec.fnMap g hsp (X.germToFunctionField V a) = Y.germToFunctionField (g ⁻¹ᵁ V) (g.app V a) := by
  have h1 : genericPoint X ∈ V := gen_mem (Classical.arbitrary V).2
  have h2 : genericPoint Y ∈ g ⁻¹ᵁ V := gen_mem (Classical.arbitrary (g ⁻¹ᵁ V)).2
  have := TrueGeo.SmallSec.fnMap_fnOf g hsp h1 h2 a
  exact this

theorem sum_ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (g : Y ⟶ X) (hη : g (genericPoint Y) = genericPoint X)
    (hsp : g (genericPoint Y) ⤳ genericPoint X) (z : X) (hz : Order.coheight z = 1)
    (hfin : (g ⁻¹' {z}).Finite) (hcod : ∀ w, g w = z → Order.coheight w = 1) (V : X.Opens)
    (hV : IsAffineOpen V) (hzV : z ∈ V) [IsFinite (g ∣_ V)] (f : X.functionField) (hf : f ≠ 0) :
    ∑ᶠ w ∈ g ⁻¹' {z}, Scheme.ord (TrueGeo.SmallSec.fnMap g hsp f) w * (g.residueDegree w : ℤ) =
      (g.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  obtain ⟨hU, hfinR⟩ := finite_app g hV
  have hηU : genericPoint Y ∈ g ⁻¹ᵁ V := by
    show g (genericPoint Y) ∈ V
    rw [hη]; exact gen_mem hzV
  haveI : Nonempty (g ⁻¹ᵁ V) := ⟨⟨_, hηU⟩⟩
  letI : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  haveI : Module.Finite Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := hfinR
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hinj : Function.Injective (algebraMap Γ(X, V) Γ(Y, g ⁻¹ᵁ V)) := by
    intro a b h
    apply X.germToFunctionField_injective V
    apply (TrueGeo.SmallSec.fnMap g hsp).injective
    rw [fnMap_germ, fnMap_germ]
    exact congrArg _ h
  have hP := height_primeIdealOf hV z hzV hz
  have key : ∀ a : Γ(X, V), a ≠ 0 →
      ∑ᶠ w ∈ g ⁻¹' {z}, Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (X.germToFunctionField V a)) w *
        (g.residueDegree w : ℤ) =
      (g.residueDegree (genericPoint Y) : ℤ) * Scheme.ord (X.germToFunctionField V a) z := by
    intro a ha
    have ha' : g.app V a ≠ 0 := fun h => ha (hinj (by rw [map_zero]; exact h))
    rw [ord_germ_eq X V hV z hzV hz a ha,
      residueDegree_genericPoint_eq_finrank X Y g V hV hU hfinR hinj,
      ← sum_ord_inertiaDeg Γ(X, V) Γ(Y, g ⁻¹ᵁ V) hinj _ hP a ha]
    classical
    refine finsum_mem_eq_of_bijOn
      (fun w => if hw : w ∈ g ⁻¹ᵁ V then hU.primeIdealOf ⟨w, hw⟩ else hU.primeIdealOf ⟨_, hηU⟩)
      ⟨?_, ?_, ?_⟩ ?_
    · intro w hw
      have hw' : w ∈ g ⁻¹ᵁ V := by
        show g w ∈ V
        rw [show g w = z from hw]; exact hzV
      simp only [Set.mem_setOf_eq, dif_pos hw']
      exact (comap_primeIdealOf g hV hU w hw').trans
        (congrArg (fun x => (hV.primeIdealOf x).asIdeal) (Subtype.ext hw))
    · intro w₁ hw₁ w₂ hw₂ h
      have h₁ : w₁ ∈ g ⁻¹ᵁ V := by
        show g w₁ ∈ V
        rw [show g w₁ = z from hw₁]; exact hzV
      have h₂ : w₂ ∈ g ⁻¹ᵁ V := by
        show g w₂ ∈ V
        rw [show g w₂ = z from hw₂]; exact hzV
      simp only [dif_pos h₁, dif_pos h₂] at h
      have e₁ := hU.fromSpec_primeIdealOf ⟨w₁, h₁⟩
      have e₂ := hU.fromSpec_primeIdealOf ⟨w₂, h₂⟩
      rw [h] at e₁
      exact e₁.symm.trans e₂
    · intro Q hQ
      have hQU : hU.fromSpec Q ∈ g ⁻¹ᵁ V := by
        rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨Q, rfl⟩
      have hQ' : hU.primeIdealOf ⟨_, hQU⟩ = Q :=
        hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hQU⟩)
      have hgw : g (hU.fromSpec Q) = z := by
        have c := comap_primeIdealOf g hV hU _ hQU
        rw [hQ'] at c
        have c2 : hV.primeIdealOf ⟨g (hU.fromSpec Q), hQU⟩ = hV.primeIdealOf ⟨z, hzV⟩ :=
          PrimeSpectrum.ext (c.symm.trans hQ)
        have d1 := hV.fromSpec_primeIdealOf ⟨g (hU.fromSpec Q), hQU⟩
        have d2 := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
        rw [c2] at d1
        exact d1.symm.trans d2
      refine ⟨hU.fromSpec Q, hgw, ?_⟩
      simp only [dif_pos hQU]
      exact hQ'
    · intro w hw
      have hw' : w ∈ g ⁻¹ᵁ V := by
        show g w ∈ V
        rw [show g w = z from hw]; exact hzV
      have hd : (if hw : w ∈ g ⁻¹ᵁ V then hU.primeIdealOf ⟨w, hw⟩ else hU.primeIdealOf ⟨_, hηU⟩) =
          hU.primeIdealOf ⟨w, hw'⟩ := dif_pos hw'
      beta_reduce
      rw [hd, fnMap_germ, ord_germ_eq Y (g ⁻¹ᵁ V) hU w hw' (hcod w hw) _ ha',
        GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart X Y g V hV hU w hw']
      rfl
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, V)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap Γ(X, V) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective V)).2 hb0
  have hA : algebraMap Γ(X, V) X.functionField a ≠ 0 := by
    intro h; apply hf; rw [h, zero_div]
  have ha0 : a ≠ 0 := by rintro rfl; exact hA (map_zero _)
  have hFA : TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField a) ≠ 0 :=
    (map_ne_zero _).2 hA
  have hFB : TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField b) ≠ 0 :=
    (map_ne_zero _).2 hB
  rw [map_div₀, ord_div hA hB]
  have e : ∀ w, Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField a) /
      TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField b)) w * (g.residueDegree w : ℤ) =
      Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField a)) w * (g.residueDegree w : ℤ) -
      Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField b)) w * (g.residueDegree w : ℤ) := by
    intro w; rw [ord_div hFA hFB, sub_mul]
  simp_rw [e]
  have hs := finsum_mem_sub_distrib
    (f := fun w => Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField a)) w *
      (g.residueDegree w : ℤ))
    (g := fun w => Scheme.ord (TrueGeo.SmallSec.fnMap g hsp (algebraMap Γ(X, V) X.functionField b)) w *
      (g.residueDegree w : ℤ)) hfin
  rw [hs]
  have ka := key a ha0
  have kb := key b hb0
  rw [mul_sub]
  exact congrArg₂ (· - ·) ka kb

theorem sum_ord_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ z : X, Order.coheight z = 1 → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ w ∈ g ⁻¹' {z}, Scheme.ord (TrueGeo.SmallSec.fnMap g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) f) w * (g.residueDegree w : ℤ) = (g.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη hdeg z hz f hf
  obtain ⟨hfin, hcod, V, hV, hzV, hgV⟩ := GlobalTheory.T.genericallyFinite_finite_near_codimOne_point k X Y p q hp hq g hg hη hdeg z hz
  exact sum_ord_fnMap g hη _ z hz hfin hcod V hV hzV f hf

end GlobalTheory.OrdPull
