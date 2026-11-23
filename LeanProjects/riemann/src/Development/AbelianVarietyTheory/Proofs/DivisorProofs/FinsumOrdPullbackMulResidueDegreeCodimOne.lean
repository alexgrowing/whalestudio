import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdMulInertiaDegEqFinrankMulOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaDegBotEqFinrankFiniteDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.OrdPush

theorem ord_ringEquiv {T T' : Type*} [CommRing T] [CommRing T'] (e : T ≃+* T') (x : T) :
    Ring.ord T' (e x) = Ring.ord T x := by
  let _ : Algebra T T' := e.toRingHom.toAlgebra
  let e' : T ≃ₐ[T] T' := { e with commutes' := fun _ => rfl }
  unfold Ring.ord
  rw [← Module.length_eq_of_surjective (S := T) (R := T') e.surjective]
  refine (Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) e' ?_).toLinearEquiv.length_eq.symm
  rw [Ideal.map_span, Set.image_singleton]
  rfl

theorem ord_isLocalization {S : Type*} [CommRing S] (M : Submonoid S) (T T' : Type*) [CommRing T]
    [CommRing T'] [Algebra S T] [Algebra S T'] [IsLocalization M T] [IsLocalization M T'] (s : S) :
    Ring.ord T' (algebraMap S T' s) = Ring.ord T (algebraMap S T s) := by
  rw [← (IsLocalization.algEquiv M T T').commutes s]
  exact ord_ringEquiv (IsLocalization.algEquiv M T T').toRingEquiv _

theorem inertiaDeg_isLocalization {S : Type*} [CommRing S] (M : Submonoid S) (B : Type*)
    [CommRing B] [Algebra S B] [IsLocalization M B] (Q : Ideal B) [Q.IsPrime] :
    Q.inertiaDeg S = 1 := by
  rw [ResidueDegreeChart.inertiaDeg_eq_finrank_of_ker (K := Q.ResidueField) (L := Q.ResidueField)
    ((algebraMap B Q.ResidueField).comp (algebraMap S B)) (algebraMap B Q.ResidueField) Q
    (fun s => Ideal.algebraMap_residueField_eq_zero.symm) ?_ ?_ (fun _ => rfl), Module.finrank_self]
  · intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨a₁, a₂⟩, ha⟩ := IsLocalization.surj M a
    obtain ⟨⟨b₁, b₂⟩, hb⟩ := IsLocalization.surj M b
    have h₁ := ((IsLocalization.map_units B a₂).map (algebraMap B Q.ResidueField)).ne_zero
    have h₂ := ((IsLocalization.map_units B b₂).map (algebraMap B Q.ResidueField)).ne_zero
    refine ⟨a₁ * b₂, b₁ * a₂, ?_⟩
    simp only [RingHom.comp_apply, map_mul] at ha hb ⊢
    rw [← ha, ← hb, map_mul, map_mul, mul_assoc, mul_assoc, mul_comm (algebraMap B _ (algebraMap S B b₂)),
      mul_div_mul_right _ _ (mul_ne_zero h₁ h₂)]
    rfl
  · intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨a, b, rfl⟩

theorem finsum_ord_mul_inertiaDeg (R S A : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    (p : PrimeSpectrum R) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra R A] [IsLocalization.AtPrime A p.asIdeal] (hdim : ringKrullDim A = 1)
    (a : R) (ha : a ≠ 0) :
    ∑ᶠ Q ∈ {Q : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) Q = p},
      ((Ring.ord (Localization.AtPrime Q.asIdeal)
        (algebraMap S _ (algebraMap R S a))).toNat : ℤ) * (Q.asIdeal.inertiaDeg R : ℤ) =
      (Module.finrank R S : ℤ) * ((Ring.ord A (algebraMap R A a)).toNat : ℤ) := by
  let M := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization M
  have hp0 : p.asIdeal.primeCompl ≤ nonZeroDivisors R := p.asIdeal.primeCompl_le_nonZeroDivisors
  have hM0 : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero (hp0 hr)))
  have : IsDomain B := IsLocalization.isDomain_localization hM0
  let _ : Algebra A B := localizationAlgebra p.asIdeal.primeCompl S
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S B]
    exact (IsLocalization.map_eq (T := M) (S := A) (Q := B) _ r).symm
  have : Module.Finite A B := Module.Finite.of_isLocalization R S p.asIdeal.primeCompl
  have hAB : Function.Injective (algebraMap A B) := localizationAlgebra_injective A B hinj
  have ha' : algebraMap R A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A hp0)).2 ha
  have hdeg : ∀ Q : PrimeSpectrum B,
      Q.asIdeal.inertiaDeg A = (Q.asIdeal.under S).inertiaDeg R := fun Q => by
    have h₁ := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under S) Q.asIdeal
    have h₂ := Ideal.inertiaDeg_tower (R := R) (Q.asIdeal.under A) Q.asIdeal
    rw [inertiaDeg_isLocalization M B, mul_one] at h₁
    rw [inertiaDeg_isLocalization p.asIdeal.primeCompl A, one_mul] at h₂
    exact h₂.symm.trans h₁
  have hrk : Module.finrank A B = Module.finrank R S := by
    rw [← inertiaDeg_bot_eq_finrank A B hAB, ← inertiaDeg_bot_eq_finrank R S hinj]
    refine (hdeg ⊥).trans ?_
    congr 1
    exact Ideal.comap_bot_of_injective _ (IsLocalization.injective B hM0)
  rw [← hrk, ← finsum_ord_mul_inertiaDeg_eq_finrank_mul_ord A B hAB hdim _ ha']
  symm
  have hmax : (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = p.asIdeal :=
    IsLocalization.AtPrime.under_maximalIdeal A p.asIdeal
  have hsq : ∀ Q : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) =
      PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap (algebraMap A B) Q) := fun Q => by
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine finsum_mem_eq_of_bijOn (PrimeSpectrum.comap (algebraMap S B)) ⟨?_, ?_, ?_⟩ ?_
  · intro Q hQ
    change _ = p
    rw [hsq]
    ext1
    rw [← hmax, ← show Q.asIdeal.comap (algebraMap A B) = _ from hQ]
    rfl
  · exact (PrimeSpectrum.localization_comap_injective B M).injOn
  · intro Q hQ
    have hQ' : PrimeSpectrum.comap (algebraMap R S) Q = p := hQ
    have : Q ∈ Set.range (PrimeSpectrum.comap (algebraMap S B)) := by
      rw [PrimeSpectrum.localization_comap_range B M]
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨r, hr, rfl⟩ h
      exact hr (by rw [← hQ']; exact h)
    obtain ⟨Q', rfl⟩ := this
    refine ⟨Q', ?_, rfl⟩
    have := PrimeSpectrum.localization_comap_injective A p.asIdeal.primeCompl
      (a₁ := PrimeSpectrum.comap (algebraMap A B) Q') (a₂ := IsLocalRing.closedPoint A)
      (by rw [← hsq, hQ']; ext1; exact hmax.symm)
    exact congrArg PrimeSpectrum.asIdeal this
  · intro Q _
    rw [hdeg]
    congr 3
    have : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal)
        (PrimeSpectrum.comap (algebraMap S B) Q).asIdeal :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q.asIdeal) Q.asIdeal
    rw [← IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R S B,
      ← IsScalarTower.algebraMap_apply S B]
    exact ord_isLocalization (PrimeSpectrum.comap (algebraMap S B) Q).asIdeal.primeCompl _ _ _

theorem height_eq_one {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (Q : PrimeSpectrum S) (h : (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal.height = 1) :
    Q.asIdeal.height = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← h, PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
    exact Order.height_le_height_apply_of_strictMono _
      (fun a b hab => Ideal.IsIntegral.comap_lt_comap (R := R) (I := a.asIdeal) hab) Q
  · rw [Order.one_le_iff_ne_zero]
    intro h0
    have hQ : Q.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.1 h0
    rw [PrimeSpectrum.comap_asIdeal, hQ, Ideal.comap_bot_of_injective _ hinj, Ideal.height_bot] at h
    exact zero_ne_one h

theorem coheight_eq_height {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) : Order.coheight x = (hV.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

theorem ord_fnOf {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {V : X.Opens}
    (hV : IsAffineOpen V) (x : X) (hx : x ∈ V) (h1 : Order.coheight x = 1) (a : Γ(X, V))
    (ha : a ≠ 0) : Scheme.ord (fnOf V (gen_mem hx) a) x =
      (Ring.ord (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
        (algebraMap Γ(X, V) _ a)).toNat := by
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← algebraMap_germ hx, ord_algebraMap h1
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral X x hx)).2 ha),
    ord_isLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)]
  rfl

theorem exists_affine {X Y : Scheme.{0}} (π : Y ⟶ X) (z : X) (U : X.Opens) (hz : z ∈ U)
    [IsFinite (π ∣_ U)] : ∃ V : X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen (π ⁻¹ᵁ V) ∧
      (π.app V).hom.Finite := by
  obtain ⟨_, ⟨V', hV', rfl⟩, hzV, -⟩ := (U : Scheme.{0}).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (⟨z, hz⟩ : U)) isOpen_univ
  refine ⟨U.ι ''ᵁ V', ⟨⟨z, hz⟩, hzV, rfl⟩, hV'.image_of_isOpenImmersion _, ?_, ?_⟩
  · rw [← image_morphismRestrict_preimage]
    exact (IsAffineOpen.preimage hV' (π ∣_ U)).image_of_isOpenImmersion _
  · have h := (π ∣_ U).finite_app V' hV'
    rw [morphismRestrict_app] at h
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).1 h

theorem finsum_ord_fnOf {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X)
    (h1 : Order.coheight z = 1) (V : X.Opens) (hz : z ∈ V) (hV : IsAffineOpen V)
    (hW : IsAffineOpen (π ⁻¹ᵁ V)) (hfin : (π.app V).hom.Finite) (a : Γ(X, V)) (ha : a ≠ 0) :
    ∑ᶠ w ∈ {w : Y | π w = z},
      Scheme.ord (TrueGeo.SmallSec.fnMap π hη (fnOf V (gen_mem hz) a)) w *
        (π.residueDegree w : ℤ) =
      (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord (fnOf V (gen_mem hz) a) z := by
  have hgen : genericPoint Y ∈ π ⁻¹ᵁ V := hη.mem_open V.isOpen (gen_mem hz)
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  have : Nonempty (π ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hgen⟩⟩
  let _ : Algebra Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  have : Module.Finite Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := hfin
  have hinj : Function.Injective (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) := by
    intro s t hst
    apply germ_injective_of_isIntegral X (genericPoint X) (gen_mem hz)
    apply (TrueGeo.SmallSec.fnMap π hη).injective
    exact (TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen s).trans
      ((congrArg (fnOf _ hgen) hst).trans (TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen t).symm)
  have hcomap : ∀ (w : Y) (hw : w ∈ π ⁻¹ᵁ V),
      PrimeSpectrum.comap (algebraMap Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) (hW.primeIdealOf ⟨w, hw⟩) =
        hV.primeIdealOf ⟨π w, hw⟩ := fun w hw => by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := π) V hV _ hW le_rfl hw
    rwa [Scheme.Hom.appLE_eq_app] at h
  have hp1 : (hV.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    rw [← coheight_eq_height, h1]
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have key := finsum_ord_mul_inertiaDeg Γ(X, V) Γ(Y, π ⁻¹ᵁ V)
    (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) hinj (hV.primeIdealOf ⟨z, hz⟩)
    (by rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨z, hz⟩).asIdeal, hp1]; rfl)
    a ha
  have hrk : π.residueDegree (genericPoint Y) = Module.finrank Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := by
    rw [ResidueDegreeChart.residueDegree_eq_inertiaDeg X Y π V hV hW _ hgen,
      ← inertiaDeg_bot_eq_finrank _ _ hinj]
    congr 1
    rw [hW.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  rw [hrk, ord_fnOf hV z hz h1 a ha, ← key, TrueGeo.SmallSec.fnMap_fnOf π hη _ hgen]
  symm
  have hmem : ∀ Q : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V), hW.fromSpec Q ∈ π ⁻¹ᵁ V := fun Q => by
    have : hW.fromSpec Q ∈ Set.range hW.fromSpec := ⟨Q, rfl⟩
    rwa [hW.range_fromSpec] at this
  have hinv : ∀ Q : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V), hW.primeIdealOf ⟨_, hmem Q⟩ = Q := fun Q =>
    hW.fromSpec.isOpenEmbedding.injective (hW.fromSpec_primeIdealOf _)
  refine finsum_mem_eq_of_bijOn (fun Q => hW.fromSpec Q) ⟨?_, ?_, ?_⟩ ?_
  · intro Q hQ
    have h := hcomap _ (hmem Q)
    rw [hinv, show PrimeSpectrum.comap _ Q = _ from hQ] at h
    have h' := congrArg (fun q => hV.fromSpec q) h
    simp only [hV.fromSpec_primeIdealOf] at h'
    exact h'.symm
  · exact hW.fromSpec.isOpenEmbedding.injective.injOn
  · intro w hw
    have hw' : π w = z := hw
    subst hw'
    exact ⟨hW.primeIdealOf ⟨w, hz⟩, hcomap w hz, hW.fromSpec_primeIdealOf _⟩
  · intro Q hQ
    have hc : Order.coheight (hW.fromSpec Q) = 1 := by
      rw [coheight_eq_height hW _ (hmem Q), hinv]
      exact height_eq_one hinj Q (by rw [show PrimeSpectrum.comap _ Q = _ from hQ, hp1])
    have h₁ := ord_fnOf hW _ (hmem Q) hc (algebraMap Γ(X, V) _ a) ((map_ne_zero_iff _ hinj).2 ha)
    have h₂ := ResidueDegreeChart.residueDegree_eq_inertiaDeg X Y π V hV hW _ (hmem Q)
    rw [hinv] at h₁ h₂
    rw [h₂]
    exact congrArg (· * _) h₁.symm

theorem finite_fibre {X Y : Scheme.{0}} (π : Y ⟶ X) (z : X) (U : X.Opens) (hz : z ∈ U)
    [IsFinite (π ∣_ U)] : {w : Y | π w = z}.Finite := by
  have h := (π ∣_ U).finite_preimage_singleton ⟨z, hz⟩
  refine (h.image (π ⁻¹ᵁ U).ι).subset ?_
  intro w hw
  have hw' : π w = z := hw
  subst hw'
  exact ⟨⟨w, hz⟩, Subtype.ext (morphismRestrict_base_coe π U ⟨w, hz⟩), rfl⟩

theorem finsum_ord_fnMap_mul_residueDegree : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (π : Y ⟶ X) (hη : π (genericPoint Y) ⤳ genericPoint X) (z : X), Order.coheight z = 1 → (∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U)) → ∀ f : X.functionField, f ≠ 0 → ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη f) w * (π.residueDegree w : ℤ) = (π.residueDegree (genericPoint Y) : ℤ) * Scheme.ord f z := by
  rintro X Y _ _ _ _ π hη z h1 ⟨U, hU, hfin⟩ f hf
  obtain ⟨V, hz, hV, hW, hF⟩ := exists_affine π z U hU
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, V)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : fnOf V (gen_mem hz) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ(X, V) X.functionField)).2 hb0
  have e : fnOf V (gen_mem hz) a = f * fnOf V (gen_mem hz) b :=
    (div_eq_iff hb').1 hab
  have ha0 : a ≠ 0 := fun h => mul_ne_zero hf hb' (by rw [← e, h, map_zero])
  have h₁ := finsum_ord_fnOf π hη z h1 V hz hV hW hF a ha0
  have h₂ := finsum_ord_fnOf π hη z h1 V hz hV hW hF b hb0
  have hi := (TrueGeo.SmallSec.fnMap π hη).injective
  have hf' := (map_ne_zero_iff _ hi).2 hf
  have hb'' := (map_ne_zero_iff _ hi).2 hb'
  rw [e, map_mul] at h₁
  simp only [Scheme.ord_mul hf hb', Scheme.ord_mul hf' hb'',
    add_mul, mul_add] at h₁
  rw [finsum_mem_add_distrib (finite_fibre π z U hU), h₂] at h₁
  exact add_right_cancel h₁

end GlobalTheory.OrdPush
