import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.DominatesIffIsLocalHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open MvPolynomial in
private lemma ne_zero_of_eval₂Hom_formallyEtale {A T : Type} [CommRing A] [CommRing T] [Nontrivial T]
    {n : ℕ} (ι : A →+* T) (τ : Fin n → T) (h : (MvPolynomial.eval₂Hom ι τ).FormallyEtale) (i : Fin n) :
    τ i ≠ 0 := by
  letI := (eval₂Hom ι τ).toAlgebra
  have hE : Algebra.FormallyEtale (MvPolynomial (Fin n) A) T := h
  let g : MvPolynomial (Fin n) A →+* DualNumber T :=
    eval₂Hom ((TrivSqZeroExt.inlHom T T).comp ι)
      (fun j => TrivSqZeroExt.inl (τ j) + if j = i then DualNumber.eps else 0)
  letI := g.toAlgebra
  have hfst : (TrivSqZeroExt.fstHom T T T).toRingHom.comp g = eval₂Hom ι τ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [g]
    · intro j
      simp only [g, RingHom.comp_apply, eval₂Hom_X']
      split_ifs <;> simp
  let p : DualNumber T →ₐ[MvPolynomial (Fin n) A] T :=
    { (TrivSqZeroExt.fstHom T T T).toRingHom with
      commutes' := fun x => by
        show (TrivSqZeroExt.fstHom T T T).toRingHom.comp g x = _
        rw [hfst]; rfl }
  have hp : Function.Surjective p := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (p : DualNumber T →+* T)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    rw [pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  intro h0
  have hc := (Algebra.FormallySmooth.liftOfSurjective (AlgHom.id _ T) p hp hnil).commutes (X i)
  have h1 : algebraMap (MvPolynomial (Fin n) A) T (X i) = 0 := by
    rw [RingHom.algebraMap_toAlgebra, eval₂Hom_X', h0]
  have h2 : algebraMap (MvPolynomial (Fin n) A) (DualNumber T) (X i) = DualNumber.eps := by
    rw [RingHom.algebraMap_toAlgebra]; simp [g, h0]
  rw [h1, h2, map_zero] at hc
  have := congrArg TrivSqZeroExt.snd hc
  simp at this

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open MvPolynomial in
private lemma formallyEtale_quotient_last {A T : Type} [CommRing A] [CommRing T] {n : ℕ}
    (ι : A →+* T) (τ : Fin (n + 1) → T) (h : (MvPolynomial.eval₂Hom ι τ).FormallyEtale) :
    (MvPolynomial.eval₂Hom ((Ideal.Quotient.mk (Ideal.span {τ (Fin.last n)})).comp ι)
      (fun i => Ideal.Quotient.mk (Ideal.span {τ (Fin.last n)}) (τ (Fin.castSucc i)))).FormallyEtale := by
  set I : Ideal T := Ideal.span {τ (Fin.last n)} with hI
  set φ := eval₂Hom ι τ with hφ
  set φ' := eval₂Hom ((Ideal.Quotient.mk I).comp ι)
    (fun i => Ideal.Quotient.mk I (τ (Fin.castSucc i))) with hφ'
  let σ : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin n) A :=
    eval₂Hom C (Fin.lastCases 0 X)
  have hσ : ∀ p, φ' (σ p) = Ideal.Quotient.mk I (φ p) := by
    intro p
    show (φ'.comp σ) p = ((Ideal.Quotient.mk I).comp φ) p
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro a; simp [σ, φ, φ']
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp [σ, φ, φ', I, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
      · simp [σ, φ, φ']
  letI := φ.toAlgebra
  letI := φ'.toAlgebra
  have hE : Algebra.FormallyEtale (MvPolynomial (Fin (n + 1)) A) T := h
  show Algebra.FormallyEtale (MvPolynomial (Fin n) A) (T ⧸ I)
  have toT : ∀ (C' : Type) [CommRing C'] [Algebra (MvPolynomial (Fin n) A) C']
      [Algebra (MvPolynomial (Fin (n + 1)) A) C']
      (_ : ∀ p, algebraMap (MvPolynomial (Fin (n + 1)) A) C' p =
        algebraMap (MvPolynomial (Fin n) A) C' (σ p)),
      ∃ F : (T ⧸ I →ₐ[MvPolynomial (Fin n) A] C') → (T →ₐ[MvPolynomial (Fin (n + 1)) A] C'),
        Function.Bijective F ∧ ∀ f x, F f x = f (Ideal.Quotient.mk I x) := by
    intro C' _ _ _ hC
    refine ⟨fun f => { f.toRingHom.comp (Ideal.Quotient.mk I) with
      commutes' := fun p => by
        show f (Ideal.Quotient.mk I (φ p)) = _
        rw [← hσ, hC]; exact f.commutes (σ p) }, ⟨?_, ?_⟩, fun f x => rfl⟩
    · intro f₁ f₂ hf
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact DFunLike.congr_fun hf y
    · intro g
      have hg : I ≤ RingHom.ker g.toRingHom := by
        rw [hI, Ideal.span_le, Set.singleton_subset_iff]
        show g (τ (Fin.last n)) = 0
        have : τ (Fin.last n) = algebraMap (MvPolynomial (Fin (n + 1)) A) T (X (Fin.last n)) := by
          simp [RingHom.algebraMap_toAlgebra, φ]
        rw [this, g.commutes, hC]
        simp [σ]
      refine ⟨{ Ideal.Quotient.lift I g.toRingHom hg with commutes' := fun p => ?_ }, ?_⟩
      · show (Ideal.Quotient.lift I g.toRingHom hg).comp φ' p = algebraMap _ C' p
        congr 1
        apply MvPolynomial.ringHom_ext
        · intro a
          have := g.commutes (C a)
          rw [hC] at this
          simpa [φ', φ, σ, RingHom.algebraMap_toAlgebra] using this
        · intro i
          have := g.commutes (X (Fin.castSucc i))
          rw [hC] at this
          simpa [φ', φ, σ, RingHom.algebraMap_toAlgebra] using this
      · ext x; rfl
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ J hJ
  letI : Algebra (MvPolynomial (Fin (n + 1)) A) B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp σ).toAlgebra
  obtain ⟨F, hF, hFa⟩ := toT B (fun p => rfl)
  obtain ⟨G, hG, hGa⟩ := toT (B ⧸ J) (fun p => rfl)
  have hbij := Algebra.FormallyEtale.comp_bijective (MvPolynomial (Fin (n + 1)) A) T J hJ
  have hcomm : ∀ f, G ((Ideal.Quotient.mkₐ _ J).comp f) = (Ideal.Quotient.mkₐ _ J).comp (F f) := by
    intro f; ext x; simp [hFa, hGa]
  constructor
  · intro f₁ f₂ hf
    apply hF.1
    apply hbij.1
    rw [← hcomm, ← hcomm, hf]
  · intro g
    obtain ⟨f, hf⟩ := hbij.2 (G g)
    obtain ⟨f', rfl⟩ := hF.2 f
    exact ⟨f', hG.1 (by rw [hcomm, hf])⟩

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
private lemma isDomain_of_formallyEtale_of_isLocalRing {A B : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.FormallyEtale A B] : IsDomain B := by
  obtain ⟨S, M, hS, hM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra A B).1 inferInstance
  haveI : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.mp hS
  let q : Ideal S := (IsLocalRing.maximalIdeal B).comap (algebraMap S B)
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime B q := by
    refine IsLocalization.of_le M _ ?_ ?_
    · intro m hm hmq
      exact (IsLocalRing.mem_maximalIdeal _).1 hmq (IsLocalization.map_units B ⟨m, hm⟩)
    · intro y hy
      by_contra hu
      exact hy ((IsLocalRing.mem_maximalIdeal _).2 hu)
  let e : Localization.AtPrime q ≃ₐ[A] B :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B).restrictScalars A
  haveI : Algebra.FormallyEtale A (Localization.AtPrime q) := Algebra.FormallyEtale.of_equiv e.symm
  have hmem : (⟨q, hq⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus A S := by
    rw [Algebra.mem_etaleLocus_iff]; exact ‹_›
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem Algebra.isOpen_etaleLocus
  haveI : Algebra.FormallyEtale A (Localization.Away f) :=
    Algebra.basicOpen_subset_etaleLocus_iff.1 hsub
  haveI : Algebra.Etale A (Localization.Away f) :=
    ⟨inferInstance, Algebra.FinitePresentation.trans A S (Localization.Away f)⟩
  have hdisj : Disjoint (Submonoid.powers f : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hqf (hq.mem_of_pow_mem k hk)
  let q' : Ideal (Localization.Away f) := q.map (algebraMap S _)
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ q hq hdisj
  have hcomap : q'.comap (algebraMap S (Localization.Away f)) = q :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) _ hq hdisj
  obtain ⟨hdom, -⟩ := _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale A q' (Localization.AtPrime q')
  haveI : IsLocalization q.primeCompl (Localization.AtPrime q') := by
    have h1 : IsLocalization (q'.comap (algebraMap S (Localization.Away f))).primeCompl
        (Localization.AtPrime q') :=
      IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers f) q'
    have h2 : q.primeCompl = (q'.comap (algebraMap S (Localization.Away f))).primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomap]
    exact h2 ▸ h1
  let e' : Localization.AtPrime q' ≃+* B :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q') B).toRingEquiv
  exact e'.symm.toMulEquiv.isDomain

open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem _root_.GlobalTheory.FieldPair.IsEtTower.exists_quotient_last :
    ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin (r + 1) → T)
    (hT : _root_.GlobalTheory.FieldPair.IsEtTower cK R cL T ι ψ τ),
  ∃ (L' : Type) (_ : Field L') (cL' : ℂ →+* L') (T' : Subring L') (π : T →+* T') (ι' : R →+* T')
    (ψ' : T' →+* R),
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {τ (Fin.last r)} ∧ τ (Fin.last r) ≠ 0 ∧
    _root_.GlobalTheory.FieldPair.IsEtTower cK R cL' T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) ∧
    ψ'.comp π = ψ ∧ π.comp ι = ι' ∧
    ∀ a, (π ⟨cL a, hT.top.const_mem a⟩ : L') =
      cL' a := by
  intro K L _ _ cK cL r R T ι ψ τ hT
  have hne : τ (Fin.last r) ≠ 0 :=
    ne_zero_of_eval₂Hom_formallyEtale ι τ hT.etale _
  set I : Ideal T := Ideal.span {τ (Fin.last r)} with hI
  have hIt : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, hI, Ideal.mem_span_singleton]
    rintro ⟨u, hu⟩
    have h1 := congrArg ψ hu
    rw [map_mul, hT.zero, zero_mul, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (T ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  haveI : IsLocalRing T := hT.top.isLocalRing
  haveI : IsLocalRing (T ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsIntegrallyClosed R := hT.normal
  letI : Algebra ℂ R :=
    (cK.codRestrict R hT.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R :=
    hT.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsIntegrallyClosed (MvPolynomial (Fin r) R) := _root_.GlobalTheory.isIntegrallyClosed_mvPolynomial_fin R r
  letI : Algebra ℂ T :=
    (cL.codRestrict T hT.top.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T :=
    hT.top.essFiniteType
  haveI : Algebra.EssFiniteType ℂ (T ⧸ I) := Algebra.EssFiniteType.comp ℂ T (T ⧸ I)
  set φ' := MvPolynomial.eval₂Hom ((Ideal.Quotient.mk I).comp ι)
    (fun i => Ideal.Quotient.mk I (τ (Fin.castSucc i))) with hφ'
  letI : Algebra (MvPolynomial (Fin r) R) (T ⧸ I) := φ'.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin r) R) (T ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show Ideal.Quotient.mk I (algebraMap ℂ T a) = φ' (MvPolynomial.C (algebraMap ℂ R a))
      rw [hφ', MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      congr 1
      exact Subtype.ext (hT.const a).symm
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin r) R) (T ⧸ I) :=
    Algebra.EssFiniteType.of_comp ℂ _ _
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) R) (T ⧸ I) :=
    formallyEtale_quotient_last ι τ hT.etale
  haveI : IsDomain (T ⧸ I) := isDomain_of_formallyEtale_of_isLocalRing (A := MvPolynomial (Fin r) R)
  set f : (T ⧸ I) →+* FractionRing (T ⧸ I) := algebraMap _ _ with hf_def
  have hf : Function.Injective f := IsFractionRing.injective _ _
  let e : (T ⧸ I) ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (by simpa using congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hψI : I ≤ RingHom.ker ψ := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hT.zero _
  let ψQ : (T ⧸ I) →+* R := Ideal.Quotient.lift I ψ hψI
  let π : T →+* f.range := (e : (T ⧸ I) →+* f.range).comp (Ideal.Quotient.mk I)
  refine ⟨FractionRing (T ⧸ I), inferInstance, f.comp ((Ideal.Quotient.mk I).comp
    (cL.codRestrict T hT.top.const_mem)), f.range, π,
    π.comp ι, ψQ.comp (e.symm : f.range →+* (T ⧸ I)), ?_, ?_, hne, ?_, ?_, rfl, fun a => rfl⟩
  · exact e.surjective.comp Ideal.Quotient.mk_surjective
  · ext x
    simp only [RingHom.mem_ker]
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ e.injective]
    rfl
  · refine ⟨hT.base, hT.normal, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun a => ⟨_, rfl⟩, ?_, ?_, ?_⟩
      · exact IsLocalRing.of_surjective' (e : (T ⧸ I) →+* f.range) e.surjective
      · have h1 : (algebraMap ℂ (T ⧸ I)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
        have h2 := h1.comp (RingHom.FiniteType.of_surjective (e : (T ⧸ I) →+* f.range)
          e.surjective).essFiniteType
        exact h2
      · intro z
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T ⧸ I) z
        have hb' : f b ≠ 0 := (map_ne_zero_iff _ hf).2 (nonZeroDivisors.ne_zero hb)
        exact ⟨f a, ⟨a, rfl⟩, f b, ⟨b, rfl⟩, hb', div_mul_cancel₀ _ hb'⟩
    · intro a
      show f (Ideal.Quotient.mk I (ι _)) = f (Ideal.Quotient.mk I _)
      congr 2
      exact Subtype.ext (hT.const a)
    · intro a
      show ψQ (e.symm (e (Ideal.Quotient.mk I (ι a)))) = a
      rw [RingEquiv.symm_apply_apply]
      exact hT.retr a
    · intro i
      show ψQ (e.symm (e (Ideal.Quotient.mk I (τ (Fin.castSucc i))))) = 0
      rw [RingEquiv.symm_apply_apply]
      exact hT.zero _
    · have heq : MvPolynomial.eval₂Hom (π.comp ι) (fun i => π (τ (Fin.castSucc i))) =
          (e : (T ⧸ I) →+* f.range).comp φ' := by
        apply MvPolynomial.ringHom_ext <;> intro <;> simp [π, φ']
      rw [heq]
      letI := ((e : (T ⧸ I) →+* f.range).comp φ').toAlgebra
      exact Algebra.FormallyEtale.of_equiv
        { e with commutes' := fun p => rfl : (T ⧸ I) ≃ₐ[MvPolynomial (Fin r) R] f.range }
  · refine RingHom.ext fun x => ?_
    show ψQ (e.symm (e (Ideal.Quotient.mk I x))) = ψ x
    rw [RingEquiv.symm_apply_apply]
    rfl

end GlobalTheory.FieldPair
