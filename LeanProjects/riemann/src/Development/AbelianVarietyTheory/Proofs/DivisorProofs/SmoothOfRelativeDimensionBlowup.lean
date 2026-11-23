import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartAtSiegelBlowupPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartCentreIsCompletedEtaleLocalMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveOfIsCplAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped TensorProduct

namespace GlobalTheory.BlowSmooth

theorem formallySmooth_of_regular_fibre {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing B]
    [IsLocalRing B] (σ : A →+* B) [IsLocalHom σ] [PerfectField (ResidueField A)] (hf : σ.Flat) (he : σ.EssFiniteType)
    (hr : IsRegularLocalRing (B ⧸ (maximalIdeal A).map σ)) : σ.FormallySmooth := by
  algebraize [σ]
  have : IsLocalHom (algebraMap A B) := ‹_›
  let e : (B ⧸ (maximalIdeal A).map σ) ≃+* ResidueField A ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ maximalIdeal A)).toRingEquiv
  have : IsRegularLocalRing (ResidueField A ⊗[A] B) := .of_ringEquiv e
  have : Algebra.FormallySmooth (ResidueField A) (ResidueField A ⊗[A] B) :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _
  have : Algebra.FinitePresentation A (Algebra.EssFiniteType.subalgebra A B) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := A) (S := B)
    (Algebra.EssFiniteType.submonoid A B)

theorem isRegularLocalRing_quotient_of_flat {B R : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
    [IsLocalRing R] (φ : B →+* R) (hf : φ.Flat) (hm : (maximalIdeal B).map φ = maximalIdeal R) (I : Ideal B) (hI : I ≠ ⊤)
    (hr : IsRegularLocalRing (R ⧸ I.map φ)) : IsRegularLocalRing (B ⧸ I) := by
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let χ : (B ⧸ I) →+* (R ⧸ I.map φ) := Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map
  have hcomm : (Ideal.Quotient.mk (I.map φ)).comp φ = χ.comp (Ideal.Quotient.mk I) := by
    ext a; simp [χ]
  refine (GlobalTheory.RegSmooth.isRegularLocalRing_of_flat_of_map_maximalIdeal' χ (GlobalTheory.Pat.flat_quotientMap_map φ hf I) ?_).1
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map φ)) Ideal.Quotient.mk_surjective, ← hm,
    ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
    Ideal.map_map, hcomm]

theorem perfectField_residueField {o : Type} [CommRing o] [IsDedekindDomain o] [CharZero o] [Algebra.FiniteType ℤ o]
    (q : Ideal o) [q.IsPrime] : PerfectField q.ResidueField := by
  obtain ⟨p, hp⟩ := CharP.exists q.ResidueField
  rcases CharP.char_is_prime_or_zero q.ResidueField p with h | rfl
  · have : Fact p.Prime := ⟨h⟩
    have hq : q ≠ ⊥ := by
      rintro rfl
      have h1 : algebraMap o (⊥ : Ideal o).ResidueField (p : o) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero _ p
      rw [Ideal.algebraMap_residueField_eq_zero, Ideal.mem_bot] at h1
      exact h.ne_zero (Nat.cast_eq_zero.1 h1)
    have : q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq
    have : Algebra.FiniteType ℤ q.ResidueField :=
      Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom ℤ o q.ResidueField)
        (Ideal.algebraMap_residueField_surjective q)
    let _ : Algebra (ZMod p) q.ResidueField := ZMod.algebra _ p
    have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := q.ResidueField) (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) q.ResidueField := .of_restrictScalars_finiteType ℤ _ _
    have : Module.Finite (ZMod p) q.ResidueField := finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.perfectField (ZMod p)
  · have : CharZero q.ResidueField := CharP.charP_to_charZero _
    infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem formallySmooth_stalkMap {o : Type} [CommRing o] [IsDedekindDomain o] {S : Scheme.{0}} (s : S ⟶ Sp o)
    [LocallyOfFiniteType s] (hp : ∀ (q : Ideal o) [q.IsPrime], PerfectField q.ResidueField) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hξ : ξ ≫ s = spMap b) (hb : Function.Injective b)
    (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (hr : IsRegularLocalRing (R ⧸ ((maximalIdeal R).comap b).map b)) :
    (s.stalkMap (ξ (closedPoint R))).hom.FormallySmooth := by
  set y := ξ (closedPoint R) with hy
  let φ₀ : S.presheaf.stalk y →+* R := (Scheme.stalkClosedPointTo ξ).hom
  let σ := (s.stalkMap y).hom
  let L := Localization.AtPrime (s y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of o) (s y)
  let τ : L →+* S.presheaf.stalk y := σ.comp e.inv.hom
  let ρ : o →+* S.presheaf.stalk y := τ.comp (algebraMap o L)
  have h3 : (Sp o).fromSpecStalk (s y) = Spec.map e.inv ≫ spMap (algebraMap o L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (s y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := s y)).symm
  have hb' : b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk s (x := y)
    have key : spMap b = spMap (φ₀.comp ρ) := by
      rw [← hξ, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, τ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (s y).asIdeal = (maximalIdeal R).comap b := by
    have : s y = spMap b (closedPoint R) := by
      rw [hy, ← hξ, Scheme.Hom.comp_apply]
    rw [this]; rfl
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian s
  have hφ : Function.Injective φ₀ := by
    have h1 : φ₀.Flat := het.1
    algebraize [φ₀]
    have : IsLocalHom (algebraMap (S.presheaf.stalk y) R) := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ξ).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := S.presheaf.stalk y) (B := R)
    exact FaithfulSMul.algebraMap_injective (S.presheaf.stalk y) R
  have : IsDomain (S.presheaf.stalk y) := hφ.isDomain φ₀
  have hρ : Function.Injective ρ := by
    rw [hb'] at hb
    exact Function.Injective.of_comp (f := φ₀) hb
  have hτ : τ.Flat := by
    algebraize [τ, ρ]
    have : FaithfulSMul o (S.presheaf.stalk y) := (faithfulSMul_iff_algebraMap_injective _ _).2 hρ
    have : IsScalarTower o L (S.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
    exact (Module.flat_iff_of_isLocalization L (s y).asIdeal.primeCompl (S.presheaf.stalk y)).2 inferInstance
  have hess : τ.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.FiniteType.of_surjective _ e.commRingCatIsoToRingEquiv.symm.surjective).essFiniteType
      (LocallyOfFiniteType.stalkMap s y)
  have : IsLocalHom e.inv.hom := isLocalHom_of_isIso e.inv
  have : IsLocalHom τ := RingHom.isLocalHom_comp _ _
  have : PerfectField (ResidueField L) := hp (s y).asIdeal
  have hI : ((maximalIdeal L).map τ).map φ₀ = ((maximalIdeal R).comap b).map b := by
    rw [← hq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hb']
  have hne : (maximalIdeal L).map τ ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap τ).ge)
  have hreg := isRegularLocalRing_quotient_of_flat φ₀ het.1 het.2.1 _ hne (hI ▸ hr)
  have hs := formallySmooth_of_regular_fibre τ hτ hess hreg
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso e.inv (s.stalkMap y)).1 hs

theorem smoothOfRelativeDimension_of_dense {U X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (n : ℕ) (hn : SmoothOfRelativeDimension n (j ≫ f)) : SmoothOfRelativeDimension n f := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose r W hW hr using H1.exists_dim f
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  obtain ⟨_, hu, u, rfl⟩ := hj.inter_open_nonempty _ (W x).2 ⟨x, hW x⟩
  have h₁ : SmoothOfRelativeDimension (0 + r x) ((j ∣_ W x) ≫ (W x).ι ≫ f) := have := hr x; inferInstance
  have h₂ : SmoothOfRelativeDimension (0 + n) ((j ⁻¹ᵁ W x).ι ≫ j ≫ f) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
  have e := H1.dim_unique _ h₁ h₂ ⟨u, hu⟩
  rw [zero_add, zero_add] at e
  exact e ▸ hr x

theorem smoothOfRelativeDimension_blowup : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow
  have hiz : i ≫ z = F.s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, h, -⟩, -⟩ := hmin
    exact h
  obtain ⟨hproj, hdense, hji⟩ : IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i := by
    obtain ⟨_, -, -, -, -, h₁, h₂, h₃, -⟩ := hblow
    exact ⟨h₁, h₂, h₃⟩
  have hjs : j ≫ π ≫ z = F.s := by rw [← Category.assoc, hji, hiz]
  have : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
  have : IsProper (π ≫ z) := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  have : LocallyOfFinitePresentation (π ≫ z) := inferInstance
  have : Smooth (π ≫ z) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
    rintro x -
    obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, rfl⟩ :=
      GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
    have : IsCommMonObj G₁ := hfam.1.comm
    obtain ⟨het, -⟩ :=
      GlobalTheory.T.tautologicalChart_centre_isCompletedEtaleLocalMap GlobalTheory.T.chartSeparation_data_defined_over_centre_field g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
    obtain ⟨-, -, hinj, -, -, hreg⟩ := TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
    have hξ : ξ ≫ π ≫ z = spMap C.b := by
      have h1 : jK C.R ≫ ξ ≫ π ≫ z = jK C.R ≫ spMap C.b := by
        rw [← Category.assoc, ← hy, Category.assoc, hjs, hfam.2.2.2.2]
      obtain ⟨c, hc⟩ := Spec.map_surjective (ξ ≫ π ≫ z)
      rw [← hc, jK, spMap, ← Spec.map_comp, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      rw [← hc, spMap]
      congr 1
      ext a
      exact IsFractionRing.injective C.R (FractionRing C.R) (congr($h2 a))
    exact formallySmooth_stalkMap (π ≫ z) (fun q _ => perfectField_residueField q) C.b ξ hξ hinj het hreg
  exact smoothOfRelativeDimension_of_dense (π ≫ z) j hdense _ (hjs ▸ F.smooth)

end GlobalTheory.BlowSmooth
