import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

instance isPrime_span_X_zero (m : ℕ) :
    (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero 0)).2 X_prime

theorem exists_X_zero_pow_mul {m : ℕ} {f : MvPolynomial (Fin (m + 1)) ℂ} (hf : f ≠ 0) :
    ∃ (n : ℕ) (g : MvPolynomial (Fin (m + 1)) ℂ),
      g ∉ Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)} ∧ f = X 0 ^ n * g := by
  obtain ⟨n, g, hg, e⟩ := WfDvdMonoid.max_power_factor hf
    (X_prime (R := ℂ) (i := (0 : Fin (m + 1)))).irreducible
  exact ⟨n, g, fun h => hg (Ideal.mem_span_singleton.1 h), e⟩

theorem isDVR_atPrime (m : ℕ) : IsDiscreteValuationRing
    (Localization.AtPrime (Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)})) := by
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (m + 1)) ℂ)}
  set D := Localization.AtPrime q
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0), ?_, ?_⟩
  · have hmax : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0)} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    have h0 : algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ≠ 0 := by
      intro h
      refine X_ne_zero (R := ℂ) (0 : Fin (m + 1)) ?_
      exact IsLocalization.injective D (M := q.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors q)
        (h.trans (map_zero _).symm)
    refine Prime.irreducible ?_
    rw [← Ideal.span_singleton_prime h0, ← hmax]
    infer_instance
  · intro x hx
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    have hf : f ≠ 0 := by
      rintro rfl
      exact hx (IsLocalization.mk'_zero _)
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    refine ⟨n, ?_⟩
    have hgu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g) := IsLocalization.map_units D (⟨g, hg⟩ : q.primeCompl)
    have hsu : IsUnit (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s) := IsLocalization.map_units D s
    have e : IsLocalization.mk' D (X 0 ^ n * g) s * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D s =
        algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n * algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D g := by
      rw [IsLocalization.mk'_spec, map_mul, map_pow]
    show Associated _ (IsLocalization.mk' D (X 0 ^ n * g) s)
    refine (associated_mul_unit_left (algebraMap (MvPolynomial (Fin (m + 1)) ℂ) D (X 0) ^ n) _ hgu).symm.trans ?_
    rw [← e]
    exact associated_mul_unit_left _ _ hsu

end GlobalTheory.GraphLocal.FlatPlace

namespace GlobalTheory.GraphLocal.FlatPlace

open MvPolynomial

variable {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]

theorem isUnit_of_ord_eq_zero {E : Place (algebraMap ℂ K)} (y : E.ring) (hy : (y : K) ≠ 0)
    (h0 : E.ord y = 0) : IsUnit y := by
  refine IsUnit.of_mul_eq_one (b := ⟨(y : K)⁻¹, (E.ord_nonneg_iff (inv_ne_zero hy)).1
    (by rw [E.ord_inv, h0]; simp)⟩) (Subtype.ext ?_)
  simp [hy]

theorem flat_aeval_placeAlg (k : ℕ) (R : Subring K)
    (π : R →+* κ) (E : Place (algebraMap ℂ K)) (hER : E.Contains R) (t : E.ring) (zR : Fin k → R) :
    (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
    (∀ a, algebraMap ℂ K a ∈ R) →
    (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
    Irreducible t → AlgebraicIndependent ℂ (fun i => π (zR i)) →
    (MvPolynomial.aeval (Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))) :
        MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E).toRingHom.Flat := by
  intro hπ hc hord ht hind
  set x : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
    (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E)) with hx
  set φ := (MvPolynomial.aeval x : MvPolynomial (Fin (k + 1)) ℂ →ₐ[ℂ] placeAlg E)
  set q := Ideal.span {(X 0 : MvPolynomial (Fin (k + 1)) ℂ)}

  let cR : ℂ →+* R := (algebraMap ℂ K).codRestrict R hc
  have hπc : π.comp cR = algebraMap ℂ κ := RingHom.ext fun a => hπ a (hc a)

  have hC : ∀ g : MvPolynomial (Fin k) ℂ,
      φ ((finSuccEquiv ℂ k).symm (Polynomial.C g)) = aeval (fun i : Fin k => x i.succ) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a =>
      rw [show (Polynomial.C (MvPolynomial.C a) : Polynomial (MvPolynomial (Fin k) ℂ)) =
        algebraMap ℂ _ a from rfl, AlgEquiv.commutes, AlgHom.commutes, aeval_C]
    | add p r hp hr => rw [Polynomial.C_add, map_add, map_add, hp, hr, map_add]
    | mul_X p i hp =>
      rw [Polynomial.C_mul, map_mul, map_mul, hp, ← finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply,
        map_mul, aeval_X, aeval_X]
  have hX : φ ((finSuccEquiv ℂ k).symm Polynomial.X) = x 0 := by
    rw [← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply, aeval_X]

  have key : ∀ f ∉ q, IsUnit (φ f) := by
    intro f hf
    set p := finSuccEquiv ℂ k f with hpdef
    set g := p.coeff 0
    have hfp : f = (finSuccEquiv ℂ k).symm p := by simp [p]
    have hp : p = Polynomial.X * p.divX + Polynomial.C g := (Polynomial.X_mul_divX_add p).symm
    have hg : g ≠ 0 := by
      intro h0
      apply hf
      rw [hfp, hp, h0, map_zero, add_zero, map_mul, ← finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

    set wR : R := eval₂ cR zR g
    have hwK : (wR : K) = (aeval (fun i : Fin k => x i.succ) g : placeAlg E) := by
      have e1 : (wR : K) = eval₂ (algebraMap ℂ K) (fun i => (zR i : K)) g :=
        eval₂_comp_left R.subtype cR zR g
      have e2 := (comp_aeval (R := ℂ) (fun i : Fin k => x i.succ) (placeAlg E).val).symm
      have e3 := congrArg (fun F : MvPolynomial (Fin k) ℂ →ₐ[ℂ] K => F g) e2
      simp only [AlgHom.comp_apply] at e3
      rw [e1]
      change _ = (placeAlg E).val (aeval (fun i : Fin k => x i.succ) g)
      rw [← e3]
      simp only [x, Fin.cons_succ]
      rfl
    have hπw : π wR ≠ 0 := by
      have e : π wR = aeval (fun i => π (zR i)) g := by
        rw [eval₂_comp_left π cR zR g, hπc]
        rfl
      rw [e]
      intro h0
      exact hg (hind (h0.trans (map_zero _).symm))
    have hw0 : (wR : K) ≠ 0 := by
      intro h0
      apply hπw
      rw [show wR = 0 from Subtype.ext h0, map_zero]
    have hwo : E.ord wR = 0 := by
      have h1 := (E.ord_nonneg_iff hw0).2 (hER _ wR.2)
      have h2 : ¬ 0 < E.ord wR := fun h => hπw ((hord wR hw0).2 h)
      omega
    set u : placeAlg E := aeval (fun i : Fin k => x i.succ) g
    set v : placeAlg E := φ ((finSuccEquiv ℂ k).symm p.divX)
    have hf' : φ f = x 0 * v + u := by
      rw [hfp, hp, map_add, map_mul, map_add, map_mul, hX, hC]
    let uE : E.ring := ⟨(u : K), u.2⟩
    let vE : E.ring := ⟨(v : K), v.2⟩
    have huE : IsUnit uE := isUnit_of_ord_eq_zero uE (by rw [← hwK] at *; simpa [uE, ← hwK] using hw0)
      (by simpa [uE, ← hwK] using hwo)
    let yE : E.ring := ⟨(φ f : K), (φ f).2⟩
    have hyE : yE = t * vE + uE := Subtype.ext (by simp [yE, uE, vE, hf', x])
    have hyu : IsUnit yE := by
      by_contra hn
      have hy : yE ∈ IsLocalRing.maximalIdeal E.ring := hn
      have htm : t ∈ IsLocalRing.maximalIdeal E.ring := ht.not_isUnit
      have : uE ∈ IsLocalRing.maximalIdeal E.ring := by
        have := sub_mem hy (Ideal.mul_mem_right vE _ htm)
        rwa [hyE, add_sub_cancel_left] at this
      exact this huE
    let toA : E.ring →+* placeAlg E :=
      { toFun := fun y => ⟨y, y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact hyu.map toA
  set D := Localization.AtPrime q
  haveI : IsDiscreteValuationRing D := isDVR_atPrime k
  have hunits : ∀ s : q.primeCompl, IsUnit (φ.toRingHom s) := fun s => key s.1 s.2
  let ℓ : D →+* placeAlg E := IsLocalization.lift (M := q.primeCompl) hunits
  have hcomp : ℓ.comp (algebraMap _ D) = φ.toRingHom := IsLocalization.lift_comp hunits
  have hφ0 : ∀ f, f ≠ 0 → φ f ≠ 0 := by
    intro f hf
    obtain ⟨n, g, hg, rfl⟩ := exists_X_zero_pow_mul hf
    rw [map_mul, map_pow]
    refine mul_ne_zero (pow_ne_zero _ ?_) (key g hg).ne_zero
    intro h
    apply ht.ne_zero
    have e : ((φ (X 0) : placeAlg E) : K) = t := by simp [φ, x]
    exact Subtype.ext (by rw [← e, h]; rfl)
  have hℓ : ℓ.Flat := by
    letI := ℓ.toAlgebra
    rw [RingHom.Flat, Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro a ha
    obtain ⟨⟨d, hd⟩, hda⟩ := (Submodule.mem_torsion_iff _).1 ha
    rw [Submodule.mem_bot]
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl d
    have hf : f ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hd (IsLocalization.mk'_zero _)
    have hℓd : ℓ (IsLocalization.mk' D f s) ≠ 0 := by
      intro h0
      have := (IsLocalization.lift_mk'_spec hunits f 0 s).1 h0
      exact hφ0 f hf (by simpa using this)
    simp only [Submonoid.mk_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hda
    exact (mul_eq_zero.1 hda).resolve_left hℓd
  have h := (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat D q.primeCompl)).comp hℓ
  rw [hcomp] at h
  exact h

end GlobalTheory.GraphLocal.FlatPlace
