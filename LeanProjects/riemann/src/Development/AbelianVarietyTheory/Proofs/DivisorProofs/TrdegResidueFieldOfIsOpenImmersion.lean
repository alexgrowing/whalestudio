import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.StalkDim

theorem trdeg_residueField_eq_trdeg_quotient (K A : Type) [Field K] [CommRing A] [Algebra K A] (p : Ideal A)
    [p.IsPrime] : Algebra.trdeg K p.ResidueField = Algebra.trdeg K (A ⧸ p) := by
  have : FaithfulSMul K (A ⧸ p) := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul (A ⧸ p) p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective (A ⧸ p) p.ResidueField)
  have : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
    IsLocalization.isAlgebraic p.ResidueField (nonZeroDivisors (A ⧸ p))
  rw [← trdeg_add_eq K (A ⧸ p) (A := p.ResidueField), trdeg_eq_zero (R := A ⧸ p) (A := p.ResidueField),
    add_zero]

theorem dim_localization_add_trdeg (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hq : ∀ a, a ∈ q ↔ algebraMap A (Localization.AtPrime p) a = 0) :
    ∃ a b : ℕ, ringKrullDim (Localization.AtPrime p) = a ∧ Algebra.trdeg K p.ResidueField = b ∧
      Algebra.trdeg K q.ResidueField = ((a + b : ℕ) : Cardinal) := by
  have hqp : q ≤ p := by
    intro a ha
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ a).1 ((hq a).1 ha)
    exact (‹p.IsPrime›.mem_or_mem (hs ▸ p.zero_mem : (s : A) * a ∈ p)).resolve_left s.2
  set B := A ⧸ q
  set P : Ideal B := p.map (Ideal.Quotient.mk q)
  have hcomap : P.comap (Ideal.Quotient.mk q) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hqp]
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hmem : ∀ s : A, Ideal.Quotient.mk q s ∈ P ↔ s ∈ p := fun s => by
    rw [← Ideal.mem_comap, hcomap]
  let L := Localization.AtPrime P
  have hLoc : IsLocalization p.primeCompl L := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro s
      rw [IsScalarTower.algebraMap_apply A B L]
      exact IsLocalization.map_units L (⟨Ideal.Quotient.mk q s, (hmem s).not.2 s.2⟩ : P.primeCompl)
    · intro z
      obtain ⟨⟨b, t⟩, hz⟩ := IsLocalization.surj P.primeCompl z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (t : B)
      refine ⟨⟨a, ⟨s, fun h => t.2 (hs ▸ (hmem s).2 h)⟩⟩, ?_⟩
      simp only [IsScalarTower.algebraMap_apply A B L]
      rw [Ideal.Quotient.algebraMap_eq, hs]
      exact hz
    · intro x y hxy
      rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L] at hxy
      obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl L).1 hxy
      obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (t : B)
      have hup : u ∉ p := fun h => t.2 (hu ▸ (hmem u).2 h)
      have h1 : u * (x - y) ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, hu, mul_sub, sub_eq_zero]
        exact ht
      obtain ⟨v, hv⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).1 ((hq _).1 h1)
      refine ⟨⟨(v : A) * u, p.primeCompl.mul_mem v.2 hup⟩, ?_⟩
      simp only
      linear_combination hv
  let e : Localization.AtPrime p ≃ₐ[A] L := IsLocalization.algEquiv p.primeCompl _ _
  have hB : Algebra.FiniteType K B := inferInstance
  have hD := GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType K P
  have e2 : ringKrullDim (B ⧸ P) = ringKrullDim (A ⧸ p) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqp)
  obtain ⟨nB, hnB, htB⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K B
  obtain ⟨np, hnp, htp⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (A ⧸ p)
  rw [e2, hnp, hnB] at hD
  have hLdim : ringKrullDim (Localization.AtPrime p) = P.height := by
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, IsLocalization.AtPrime.ringKrullDim_eq_height P L]
  have hfin : P.height ≠ ⊤ := by
    intro h
    rw [h] at hD
    have h' : (((⊤ + np : ℕ∞)) : WithBot ℕ∞) = ((nB : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hD
    simp only [top_add, WithBot.coe_inj] at h'
    exact ENat.top_ne_coe nB h'
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← ha] at hD
  have hab : a + np = nB := by exact_mod_cast hD
  refine ⟨a, np, by rw [hLdim, ← ha]; rfl, by rw [trdeg_residueField_eq_trdeg_quotient, htp], ?_⟩
  rw [trdeg_residueField_eq_trdeg_quotient, htB, hab]

end GlobalTheory.StalkDim

namespace GlobalTheory.StalkDim

theorem exists_isOpen_forall_le_of_minimal (A : Type) [CommRing A] [IsNoetherianRing A] (q : PrimeSpectrum A)
    (hq : ∀ r : PrimeSpectrum A, r ≤ q → r = q) :
    ∃ W : Set (PrimeSpectrum A), IsOpen W ∧ q ∈ W ∧ ∀ r ∈ W, q ≤ r := by
  set M := (⊥ : Ideal A).minimalPrimes \ {q.asIdeal}
  have hM : M.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing A ⊥).diff
  refine ⟨(⋃ q' ∈ M, PrimeSpectrum.zeroLocus (q' : Set A))ᶜ, ?_, ?_, ?_⟩
  · exact (hM.isClosed_biUnion fun q' _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro q' hq' hz
    have hpr : q'.IsPrime := hq'.1.1.1
    have hle : (⟨q', hpr⟩ : PrimeSpectrum A) ≤ q := (PrimeSpectrum.mem_zeroLocus _ _).1 hz
    exact hq'.2 (congrArg PrimeSpectrum.asIdeal (hq _ hle))
  · intro r hr
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hr
    obtain ⟨q'', hq'', hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ r.asIdeal)
    by_cases h : q'' = q.asIdeal
    · show q.asIdeal ≤ r.asIdeal
      rw [← h]
      exact hle
    · exact absurd ((PrimeSpectrum.mem_zeroLocus _ _).2 hle) (hr q'' ⟨hq'', h⟩)

theorem trdeg_residueField_of_isOpenImmersion (K : Type) [Field K] {Y S : Scheme.{0}} (h : Y ⟶ S)
    [IsOpenImmersion h] (f : S ⟶ Spec (CommRingCat.of K)) (y : Y) :
    @Algebra.trdeg K (S.residueField (h y)) _ _ (Spec.preimage (S.fromSpecResidueField (h y) ≫ f)).hom.toAlgebra =
      @Algebra.trdeg K (Y.residueField y) _ _ (Spec.preimage (Y.fromSpecResidueField y ≫ h ≫ f)).hom.toAlgebra := by
  letI : Algebra K (S.residueField (h y)) := (Spec.preimage (S.fromSpecResidueField (h y) ≫ f)).hom.toAlgebra
  letI : Algebra K (Y.residueField y) := (Spec.preimage (Y.fromSpecResidueField y ≫ h ≫ f)).hom.toAlgebra
  let e : S.residueField (h y) ≅ Y.residueField y := asIso (h.residueFieldMap y)
  have he : Spec.preimage (S.fromSpecResidueField (h y) ≫ f) ≫ e.hom =
      Spec.preimage (Y.fromSpecResidueField y ≫ h ≫ f) := by
    rw [← Spec.map_inj]
    simp only [e, asIso_hom, Spec.map_comp, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  let e' : S.residueField (h y) ≃ₐ[K] Y.residueField y :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  exact e'.trdeg_eq

theorem trdeg_residueField_spec (K : Type) [Field K] (A : CommRingCat.{0}) (φ : CommRingCat.of K ⟶ A)
    (y : PrimeSpectrum A) :
    @Algebra.trdeg K ((Spec A).residueField y) _ _
        (Spec.preimage ((Spec A).fromSpecResidueField y ≫ Spec.map φ)).hom.toAlgebra =
      @Algebra.trdeg K y.asIdeal.ResidueField _ _ ((algebraMap A y.asIdeal.ResidueField).comp φ.hom).toAlgebra := by
  letI : Algebra K ((Spec A).residueField y) :=
    (Spec.preimage ((Spec A).fromSpecResidueField y ≫ Spec.map φ)).hom.toAlgebra
  letI : Algebra K y.asIdeal.ResidueField := ((algebraMap A y.asIdeal.ResidueField).comp φ.hom).toAlgebra
  let e := Scheme.Spec.residueFieldIso A y
  have he : Spec.preimage ((Spec A).fromSpecResidueField y ≫ Spec.map φ) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap A y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map e.inv)]
    rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, Spec.map_preimage, Category.assoc, Spec.map_comp φ,
      Spec.map_comp _ e.inv]
    exact (congrArg (· ≫ Spec.map φ) (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField A y)).symm
  let e' : (Spec A).residueField y ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  exact e'.trdeg_eq

end GlobalTheory.StalkDim

namespace GlobalTheory.StalkDim

theorem stalk_dim_add_trdeg (K : Type) [Field K] {S X : Scheme.{0}} (f : S ⟶ Spec (CommRingCat.of K))
    (j : X ⟶ S) (d : ℕ) [LocallyOfFiniteType f] [IsOpenImmersion j] (hdense : Dense (Set.range j))
    (hsm : SmoothOfRelativeDimension d (j ≫ f)) (hdom : ∀ x : S, IsDomain (S.presheaf.stalk x)) (x : S) :
    letI : Algebra K (S.residueField x) := (Spec.preimage (S.fromSpecResidueField x ≫ f)).hom.toAlgebra
    ∃ a b : ℕ, ringKrullDim (S.presheaf.stalk x) = a ∧ Algebra.trdeg K (S.residueField x) = b ∧ a + b = d := by
  obtain ⟨A, ι, hι, ⟨y, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  haveI : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (ι ≫ f)
  letI : Algebra K A := φ.hom.toAlgebra
  have hft : Algebra.FiniteType K A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hinst : ∀ (P : Ideal A) [P.IsPrime], (inferInstance : Algebra K P.ResidueField) =
      ((algebraMap A P.ResidueField).comp φ.hom).toAlgebra := fun P _ =>
    Algebra.algebra_ext _ _ fun r => IsScalarTower.algebraMap_apply K A P.ResidueField r

  let e : S.presheaf.stalk (ι y) ≃+* Localization.AtPrime y.asIdeal :=
    (asIso (ι.stalkMap y) ≪≫ Spec.stalkIso A y).commRingCatIsoToRingEquiv
  haveI := hdom (ι y)
  haveI : IsDomain (Localization.AtPrime y.asIdeal) := Function.Injective.isDomain e.symm.toRingHom e.symm.injective

  let q : Ideal A := RingHom.ker (algebraMap A (Localization.AtPrime y.asIdeal))
  haveI hqP : q.IsPrime := RingHom.ker_isPrime (algebraMap A (Localization.AtPrime y.asIdeal))
  obtain ⟨a, b, h1, h2, h3⟩ := dim_localization_add_trdeg K A y.asIdeal q (fun c => RingHom.mem_ker)
  have hker : ∀ r : Ideal A, r.IsPrime → r ≤ y.asIdeal → q ≤ r := by
    intro r hr hry c hc
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff y.asIdeal.primeCompl _ c).1 (RingHom.mem_ker.1 hc)
    exact (hr.mem_or_mem (hs ▸ r.zero_mem : (s : A) * c ∈ r)).resolve_left (fun h => s.2 (hry h))
  have hqy : q ≤ y.asIdeal := hker _ inferInstance le_rfl
  let qp : PrimeSpectrum A := ⟨q, hqP⟩
  have hmin : ∀ r : PrimeSpectrum A, r ≤ qp → r = qp := fun r hr =>
    le_antisymm hr (hker r.asIdeal r.isPrime ((show r.asIdeal ≤ q from hr).trans hqy))

  obtain ⟨W, hWo, hqW, hW⟩ := exists_isOpen_forall_le_of_minimal A qp hmin
  have hηX : ι qp ∈ Set.range j := by
    obtain ⟨z, ⟨r, hr, rfl⟩, w, hwz⟩ := hdense.inter_open_nonempty (ι '' W)
      (ι.isOpenEmbedding.isOpenMap W hWo) ⟨ι qp, qp, hqW, rfl⟩
    have hsp : qp ⤳ r := (PrimeSpectrum.le_iff_specializes _ _).1 (hW r hr)
    exact (hsp.map ι.continuous).mem_open j.isOpenEmbedding.isOpen_range ⟨w, hwz⟩
  obtain ⟨w, hw⟩ := hηX
  have hwmin : ∀ v : X, v ⤳ w → v = w := by
    intro v hv
    have h1 : j v ⤳ ι qp := hw ▸ hv.map j.continuous
    obtain ⟨r, hr⟩ : j v ∈ Set.range ι := h1.mem_open ι.isOpenEmbedding.isOpen_range ⟨qp, rfl⟩
    rw [← hr] at h1
    have h2 : r ⤳ qp := ι.isOpenEmbedding.isInducing.specializes_iff.1 h1
    have h3 := hmin r ((PrimeSpectrum.le_iff_specializes _ _).2 h2)
    apply j.isOpenEmbedding.injective
    rw [← hr, h3, hw]
  obtain ⟨-, hd⟩ := GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension (j ≫ f) d hsm w hwmin

  have hres : ∀ (P : PrimeSpectrum A),
      @Algebra.trdeg K (S.residueField (ι P)) _ _ (Spec.preimage (S.fromSpecResidueField (ι P) ≫ f)).hom.toAlgebra =
        Algebra.trdeg K P.asIdeal.ResidueField := by
    intro P
    rw [trdeg_residueField_of_isOpenImmersion K ι f P, ← hφ, trdeg_residueField_spec K A φ P]
    exact congrArg (fun i : Algebra K P.asIdeal.ResidueField => @Algebra.trdeg K _ _ _ i) (hinst P.asIdeal).symm
  have hq_d : Algebra.trdeg K q.ResidueField = d := by
    rw [← hres qp, ← hd]
    have key : ∀ z : S, z = j w →
        @Algebra.trdeg K (S.residueField z) _ _ (Spec.preimage (S.fromSpecResidueField z ≫ f)).hom.toAlgebra =
          @Algebra.trdeg K (X.residueField w) _ _ (Spec.preimage (X.fromSpecResidueField w ≫ j ≫ f)).hom.toAlgebra := by
      rintro z rfl
      exact trdeg_residueField_of_isOpenImmersion K j f w
    exact key _ hw.symm
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e, h1]
  · exact (hres y).trans h2
  · have : ((a + b : ℕ) : Cardinal) = d := h3.symm.trans hq_d
    exact_mod_cast this

end GlobalTheory.StalkDim

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH

namespace GlobalTheory.UChart

theorem stalk_dim_add_trdeg_of_uPoinOnX {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {Z : Scheme.{0}}
    {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z} {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z}
    {j : Xo.XF c ⟶ S} {BD : EffCartierData S} (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (x : S) :
    letI : Algebra c.F (S.residueField x) := (Spec.preimage (S.fromSpecResidueField x ≫ π ≫ zs)).hom.toAlgebra
    ∃ a b : ℕ, ringKrullDim (S.presheaf.stalk x) = a ∧ Algebra.trdeg c.F (S.residueField x) = b ∧ a + b = Dw.dim := by
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, hj, hdense, hji, -⟩, -⟩ := h
  haveI : IsOpenImmersion j := hj
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  have hsm : SmoothOfRelativeDimension Dw.dim (j ≫ π ≫ zs) := by
    rw [← Category.assoc, hji, hizs]
    exact Formalism.L2.Pj.smoothOfRelativeDimension_strK Xo c
  exact GlobalTheory.StalkDim.stalk_dim_add_trdeg c.F (π ≫ zs) j Dw.dim hdense hsm (fun y => hnorm.isDomain_stalk y) x

end GlobalTheory.UChart

namespace GlobalTheory.UChart

open IsLocalRing

theorem ringKrullDim_stalk_eq_of_isTaut {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {Z : Scheme.{0}}
    {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z} {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z}
    {j : Xo.XF c ⟶ S} {BD : EffCartierData S} (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)) (hC : IsTaut C)
    (ξ : Sp (ChartRing k m e) ⟶ S) (hξ : C.y ≫ j = jK _ ≫ ξ)
    (hfin : ((residue (ChartRing k m e)).comp (Scheme.stalkClosedPointTo ξ).hom).Finite) :
    ringKrullDim (S.presheaf.stalk (ξ (closedPoint _))) = ((m + e : ℕ) : WithBot ℕ∞) := by
  set R := ChartRing k m e
  set x := ξ (closedPoint R)
  have hmain := stalk_dim_add_trdeg_of_uPoinOnX h x
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨-, -, -, -, hji, -⟩, -⟩ := h
  set ψ := (Scheme.stalkClosedPointTo ξ).hom

  obtain ⟨τS, hτS⟩ := Spec.map_surjective (S.fromSpecStalk x ≫ π ≫ zs)
  have hξF : ξ ≫ π ≫ zs = Spec.map (τS ≫ Scheme.stalkClosedPointTo ξ) := by
    rw [Spec.map_comp, hτS, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
  have hgen : jK R ≫ ξ ≫ π ≫ zs = jK R ≫ spMap C.b := by
    rw [← Category.assoc, ← hξ, Category.assoc, ← Category.assoc j, hji, hizs, C.y_over]
  have hcomp : ψ.comp τS.hom = C.b := by
    rw [hξF] at hgen
    have h2 : (τS ≫ Scheme.stalkClosedPointTo ξ) ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) =
        CommRingCat.ofHom C.b ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
      apply Spec.map_injective
      rw [Spec.map_comp (τS ≫ Scheme.stalkClosedPointTo ξ), Spec.map_comp (CommRingCat.ofHom C.b)]
      exact hgen
    refine RingHom.ext fun a => ?_
    apply IsFractionRing.injective R (FractionRing R)
    exact congr($(h2).hom a)

  have hκ : Spec.preimage (S.fromSpecResidueField x ≫ π ≫ zs) = τS ≫ S.residue x := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, hτS]
    simp only [Scheme.fromSpecResidueField, Category.assoc]
  obtain ⟨a, b, ha, hb, hab⟩ := hmain
  rw [hκ] at hb
  obtain ⟨-, -, -, -, -, -, htaut⟩ := hC
  let ρ : S.residueField x →+* ResidueField R := IsLocalRing.ResidueField.map ψ
  letI iF : Algebra c.F (S.residueField x) := (τS ≫ S.residue x).hom.toAlgebra
  letI iR : Algebra c.F (ResidueField R) := ((residue R).comp C.b).toAlgebra
  letI iκ : Algebra (S.residueField x) (ResidueField R) := ρ.toAlgebra
  haveI : IsScalarTower c.F (S.residueField x) (ResidueField R) := IsScalarTower.of_algebraMap_eq fun r => by
    show residue R (C.b r) = ρ (IsLocalRing.residue _ (τS.hom r))
    rw [← hcomp]
    exact (IsLocalRing.ResidueField.map_residue ψ (τS.hom r)).symm
  haveI : Module.Finite (S.residueField x) (ResidueField R) := by
    have e1 : (residue R).comp ψ = ρ.comp (IsLocalRing.residue _) :=
      RingHom.ext fun a => (IsLocalRing.ResidueField.map_residue ψ a).symm
    rw [e1] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : Algebra.IsAlgebraic (S.residueField x) (ResidueField R) := Algebra.IsAlgebraic.of_finite _ _
  haveI : FaithfulSMul c.F (S.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  haveI : FaithfulSMul (S.residueField x) (ResidueField R) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have htr := trdeg_add_eq c.F (S.residueField x) (A := ResidueField R)
  rw [trdeg_eq_zero (R := S.residueField x) (A := ResidueField R), add_zero] at htr
  have htaut' : ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField R) = Dw.dim := htaut
  rw [← htr, hb] at htaut'
  have h1 : m + e + b = Dw.dim := by exact_mod_cast htaut'
  rw [ha]
  congr 1
  exact_mod_cast (by omega : a = m + e)

end GlobalTheory.UChart
