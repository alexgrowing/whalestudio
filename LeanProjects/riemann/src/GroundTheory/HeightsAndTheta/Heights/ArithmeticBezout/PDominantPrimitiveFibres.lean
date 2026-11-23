import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StDominantPrimitiveFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDominantFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveElementFibres
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

namespace DominantPrimitiveFibres

theorem exists_lift_of_isIntegral {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (algebraMap R' B') ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = φ := by
  have hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B') _ hker
  have := hP
  have hmax' : (P.comap (algebraMap R' B')).IsMaximal := hPc ▸ hmax
  letI : Field (R' ⧸ P.comap (algebraMap R' B')) := Ideal.Quotient.field _
  letI : Field (B' ⧸ P) := Ideal.Quotient.field P
  let e : (R' ⧸ P.comap (algebraMap R' B')) ≃+* ℂ :=
    (Ideal.quotEquivOfEq hPc).trans (RingHom.quotientKerEquivOfSurjective hφ)
  letI : Algebra (R' ⧸ P.comap (algebraMap R' B')) ℂ := e.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic (R' ⧸ P.comap (algebraMap R' B')) (B' ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  let f : (B' ⧸ P) →ₐ[R' ⧸ P.comap (algebraMap R' B')] ℂ := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext r
  have h1 : Ideal.Quotient.mk P (algebraMap R' B' r) =
      algebraMap (R' ⧸ P.comap (algebraMap R' B')) (B' ⧸ P) (Ideal.Quotient.mk _ r) := rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.commutes]
  change e (Ideal.Quotient.mk _ r) = φ r
  simp [e, Ideal.quotEquivOfEq_mk]

theorem exists_lift_of_ringHom {R' B' : Type*} [CommRing R'] [CommRing B'] (f : R' →+* B')
    (hf : f.IsIntegral) (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp f = φ := by
  letI := f.toAlgebra
  have : Algebra.IsIntegral R' B' := ⟨hf⟩
  exact exists_lift_of_isIntegral φ hφ hker

theorem exists_point_of_root {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (ℓ : B') (m : Polynomial R')
    (hdiv : ∀ p : Polynomial R', Polynomial.aeval ℓ p = 0 → m ∣ p) (ev : R' →+* ℂ)
    (hev : Function.Surjective ev) (τ : ℂ) (hτ : (m.map ev).IsRoot τ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = ev ∧ ψ ℓ = τ := by
  let f : Polynomial R' →+* B' := (Polynomial.aeval ℓ).toRingHom
  have hc : f.comp Polynomial.C = algebraMap R' B' := RingHom.ext fun r => Polynomial.aeval_C ℓ r
  have hfint : f.IsIntegral := by
    intro z
    obtain ⟨p, hp, hpz⟩ := Algebra.IsIntegral.isIntegral (R := R') z
    refine ⟨p.map Polynomial.C, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    exact hpz
  let evτ : Polynomial R' →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom ev)
  have hsurj : Function.Surjective evτ := fun z => by
    obtain ⟨r, rfl⟩ := hev z
    exact ⟨Polynomial.C r, by simp [evτ]⟩
  have hker : RingHom.ker f ≤ RingHom.ker evτ := by
    intro p hp
    obtain ⟨q, rfl⟩ := hdiv p hp
    rw [RingHom.mem_ker, map_mul]
    have : evτ m = 0 := hτ
    rw [this, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_lift_of_ringHom f hfint evτ hsurj hker
  refine ⟨ψ, RingHom.ext fun r => ?_, ?_⟩
  · have h := DFunLike.congr_fun hψ (Polynomial.C r)
    simpa [f, evτ] using h
  · have h := DFunLike.congr_fun hψ Polynomial.X
    simpa [f, evτ] using h

theorem dim_eq (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = ((d : ℕ) : WithBot ℕ∞) := by
  have := hQ
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = ((e : ℕ) : WithBot ℕ∞) := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ Q)
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = k at h0 hdim ⊢
    induction k using WithBot.recBotCoe with
    | bot => simp at h0
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hdim (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top d)))
      | coe k => exact ⟨k, rfl⟩
  obtain ⟨A', hA'⟩ := (hG n e Q hQ he).2.1
  have h1 := DominantFibreBound.trdeg_le Q A' hA'
  have hproj : projHom Q A = aeval (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hinj
  have h2 := hind.cardinalMk_le_trdeg
  have hde : d ≤ e := by
    have := h2.trans h1
    simpa using this
  have hed : e ≤ d := by
    rw [he] at hdim
    exact_mod_cast hdim
  rw [he, le_antisymm hed hde]

theorem exists_ann (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) (b : MvPolynomial (Fin n) ℂ ⧸ Q) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧ Polynomial.aeval b g = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
  have hinj' : Function.Injective ((Ideal.Quotient.mkₐ ℂ Q).comp (aeval (linPoly A))) := hinj
  obtain ⟨g, hg0, hgb⟩ :=
    DominantFibreBound.exists_poly hG Q (linPoly A) hQ (dim_eq hG Q A hQ hdim hinj) hinj' b
  refine ⟨g, hg0, ?_⟩
  have hproj : projHom Q A = aeval (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hRB' : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) =
      (aeval fun i => Ideal.Quotient.mk Q (linPoly A i)).toRingHom := by
    rw [← hproj]
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hRB']
  exact hgb

theorem proof (hG : GenericProjectionFinite.Statement) : DominantPrimitiveFibres.Statement := by
  intro n d Q A hQ hdim hinj
  have := hQ
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
  have hRB : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q)) := hinj
  choose g hg0 hgx using fun j : Fin n =>
    exists_ann hG Q A hQ hdim hinj (Ideal.Quotient.mk Q (X j))
  set a : MvPolynomial (Fin d) ℂ := ∏ j, (g j).leadingCoeff with ha_def
  have ha : a ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  have hM : Submonoid.powers a ≤ nonZeroDivisors (MvPolynomial (Fin d) ℂ) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have hMB : (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)) ≤ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ Q) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero fun h =>
      nonZeroDivisors.ne_zero (hM hr) (hRB (by rw [h, map_zero]))
  have : IsDomain (Localization.Away a) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have : IsIntegrallyClosed (Localization.Away a) := isIntegrallyClosed_of_isLocalization _ _ hM
  have : IsDomain (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) := IsLocalization.isDomain_of_le_nonZeroDivisors (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) hMB
  have hRRA : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)) := IsLocalization.injective _ hM
  have hRABA : Function.Injective (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) :=
    localizationAlgebra_injective (M := Submonoid.powers a) (S := (MvPolynomial (Fin n) ℂ ⧸ Q)) (Rₘ := (Localization.Away a)) (Sₘ := (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) hRB
  have hsq : ∀ r : MvPolynomial (Fin d) ℂ, algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) r) =
      algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a) r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

  set xb : Fin n → (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) := fun j => algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (Ideal.Quotient.mk Q (X j)) with hxb
  have hadj : Algebra.adjoin (Localization.Away a) (Set.range xb) = ⊤ := by
    have hB := PrimitiveElementFibres.adjoin_eq_top Q A
    have hb : ∀ b : (MvPolynomial (Fin n) ℂ ⧸ Q), algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) b ∈ Algebra.adjoin (Localization.Away a) (Set.range xb) := by
      intro b
      have hb' : b ∈ Algebra.adjoin (MvPolynomial (Fin d) ℂ) (Set.range fun j => Ideal.Quotient.mk Q (X j)) := by
        rw [hB]; trivial
      induction hb' using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact Algebra.subset_adjoin ⟨j, rfl⟩
      | algebraMap r =>
        rw [hsq]
        exact Subalgebra.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    rw [eq_top_iff]
    intro z _
    obtain ⟨⟨b, ⟨_, r, hr, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)) z
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine mul_mem (hb b) ?_
    have h1 := IsLocalization.algebraMap_mk' (S := (MvPolynomial (Fin n) ℂ ⧸ Q)) (Rₘ := (Localization.Away a)) (Sₘ := (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) (1 : MvPolynomial (Fin d) ℂ) ⟨r, hr⟩
    rw [map_one] at h1
    rw [← h1]
    exact Subalgebra.algebraMap_mem _ _
  have hint : ∀ j, IsIntegral (Localization.Away a) (xb j) := by
    intro j
    obtain ⟨u, hu⟩ : IsUnit (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a) (g j).leadingCoeff) :=
      isUnit_of_dvd_unit (map_dvd _ (show (g j).leadingCoeff ∣ a from
        Finset.dvd_prod_of_mem (fun k => (g k).leadingCoeff) (Finset.mem_univ j)))
        (IsLocalization.Away.algebraMap_isUnit a)
    refine ⟨Polynomial.C (↑u⁻¹ : (Localization.Away a)) * (g j).map (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)), ?_, ?_⟩
    · apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      rw [Polynomial.leadingCoeff_map_of_injective hRRA, ← hu, Units.inv_mul]
    · rw [← Polynomial.aeval_def, map_mul, Polynomial.aeval_C, Polynomial.aeval_map_algebraMap, hxb,
        Polynomial.aeval_algebraMap_apply, hgx j, map_zero, mul_zero]
  have : Module.Finite (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) := by
    have hfg := fg_adjoin_of_finite (Set.finite_range xb) (by rintro _ ⟨j, rfl⟩; exact hint j)
    rw [hadj, Algebra.top_toSubmodule] at hfg
    exact ⟨hfg⟩

  obtain ⟨c, m, D, Q', hmon, -, hdiv, hD, ⟨α, β, hab⟩, hQ'⟩ :=
    PrimitiveLinearForm.exists_primitive_data hRABA ((algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)).comp C) xb hadj
  set ℓ : (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) := ∑ j, algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (((algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)).comp C) (c j)) * xb j with hℓ

  obtain ⟨⟨D0, s⟩, hDs⟩ := IsLocalization.surj (Submonoid.powers a) D
  obtain ⟨t, htM, ht⟩ := IsLocalization.integerNormalization_spec (Submonoid.powers a) m
  choose tq htqM htq using fun j => IsLocalization.integerNormalization_spec (Submonoid.powers a) (Q' j)
  have hne : ∀ r ∈ Submonoid.powers a, r ≠ 0 := fun r hr => nonZeroDivisors.ne_zero (hM hr)
  have hD0 : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hDs
    exact hD ((mul_eq_zero.1 hDs).resolve_right fun h => hne _ s.2 (hRRA (by rw [h, map_zero])))
  refine ⟨c, IsLocalization.integerNormalization (Submonoid.powers a) m, a * D0 * ∏ j, (tq j : MvPolynomial (Fin d) ℂ),
    fun j => Polynomial.C (a * s * ∏ k ∈ Finset.univ.erase j, (tq k : MvPolynomial (Fin d) ℂ)) *
      IsLocalization.integerNormalization (Submonoid.powers a) (Q' j), ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero ha hD0)
      (Finset.prod_ne_zero_iff.2 fun j _ => hne _ (htqM j))
  intro y hy
  simp only [map_mul, map_prod] at hy
  have hya : eval y a ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hy)
  have hyD0 : eval y D0 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hy)
  have hpow : ∀ r ∈ Submonoid.powers a, eval y r ≠ 0 := by
    rintro _ ⟨k, rfl⟩
    rw [map_pow]
    exact pow_ne_zero _ hya

  let ev : (Localization.Away a) →+* ℂ := IsLocalization.Away.lift a (g := eval y) (isUnit_iff_ne_zero.2 hya)
  have hev : ∀ r, ev (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a) r) = eval y r := IsLocalization.Away.lift_eq a _
  have hevc : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)) = eval y := RingHom.ext hev
  have hevD : ev D ≠ 0 := by
    intro h
    have h2 := congrArg ev hDs
    rw [map_mul, h, zero_mul, hev] at h2
    exact hyD0 h2.symm

  have hnorm : ∀ (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : Polynomial (Localization.Away a)) (r : MvPolynomial (Fin d) ℂ),
      p.map (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a)) = r • q → p.map (eval y) = Polynomial.C (eval y r) * q.map ev := by
    intro p q r h
    have h' : p.map (eval y) = (p.map (algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a))).map ev := by
      rw [Polynomial.map_map, hevc]
    rw [h', h, Algebra.smul_def, Polynomial.algebraMap_apply,
      Polynomial.map_mul, Polynomial.map_C, hev]
  have hmy := hnorm _ _ _ ht
  have hty : eval y (t : MvPolynomial (Fin d) ℂ) ≠ 0 := hpow _ htM

  have key : ∀ ψ : (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) →+* ℂ, ψ.comp (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) = ev →
      (∀ p : Polynomial (Localization.Away a), ψ (Polynomial.aeval ℓ p) = (p.map ev).eval (ψ ℓ)) ∧
      ψ ℓ = ∑ j, c j * ψ (xb j) ∧
      ∀ P : MvPolynomial (Fin n) ℂ, ψ (algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (Ideal.Quotient.mk Q P)) =
        eval (fun j => ψ (xb j)) P := by
    intro ψ hψ
    have hψr : ∀ r, ψ (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) r) = ev r := fun r => DFunLike.congr_fun hψ r
    refine ⟨fun p => ?_, ?_, fun P => ?_⟩
    · rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hψ, Polynomial.eval_map]
    · rw [hℓ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hψr, RingHom.comp_apply, hev, eval_C]
    · have h : (ψ.comp ((algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))).comp (Ideal.Quotient.mk Q))) =
          eval (fun j => ψ (xb j)) := by
        apply MvPolynomial.ringHom_ext
        · intro z
          rw [RingHom.comp_apply, RingHom.comp_apply, ← PrimitiveElementFibres.algebraMap_C_eq Q A z]
          change ψ (algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) (C z))) = _
          rw [hsq, hψr, hev, eval_C, eval_C]
        · intro j
          rw [eval_X]
          rfl
      exact DFunLike.congr_fun h P
  have hlin : ∀ (ψ : (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) →+* ℂ), ψ.comp (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) = ev → ∀ i : Fin d,
      ψ (algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (Ideal.Quotient.mk Q (pullback A (X i)))) = y i := by
    intro ψ hψ i
    change ψ (algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) (X i))) = y i
    rw [hsq, ← RingHom.comp_apply ψ, hψ, hev, eval_X]
  have hmyroot : ∀ τ, (m.map ev).IsRoot τ ↔
      ((IsLocalization.integerNormalization (Submonoid.powers a) m).map (eval y)).IsRoot τ := by
    intro τ
    rw [hmy, Polynomial.IsRoot, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_C,
      mul_eq_zero, or_iff_right hty]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hmy, Polynomial.natDegree_C_mul hty, hmon.natDegree_map,
      ← Polynomial.natDegree_map_eq_of_injective hRRA, ht, Algebra.smul_def,
      Polynomial.algebraMap_apply, Polynomial.natDegree_C_mul]
    exact fun h => hne _ htM (hRRA (by rw [h, map_zero]))
  ·
    have h := congrArg (Polynomial.map ev) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu1 : Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))⁻¹ * Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ)) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hty, Polynomial.C_1]
    have hu2 : Polynomial.C (ev D)⁻¹ * Polynomial.C (ev D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hevD, Polynomial.C_1]
    rw [hmy]
    refine ⟨Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))⁻¹ * Polynomial.C (ev D)⁻¹ * α.map ev,
      Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))⁻¹ * Polynomial.C (ev D)⁻¹ * β.map ev, ?_⟩
    rw [Polynomial.derivative_C_mul]
    linear_combination (Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))⁻¹ * Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ)) *
      Polynomial.C (ev D)⁻¹) * h + (Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))⁻¹ * Polynomial.C (eval y (t : MvPolynomial (Fin d) ℂ))) * hu2 + hu1
  ·
    intro x hx
    have hunit : ∀ s' : (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)), IsUnit (PrimitiveElementFibres.evalAt Q x hx.1 (s' : (MvPolynomial (Fin n) ℂ ⧸ Q))) := by
      rintro ⟨_, r, hr, rfl⟩
      change IsUnit (PrimitiveElementFibres.evalAt Q x hx.1 (projHom Q A r))
      rw [PrimitiveElementFibres.evalAt_projHom Q A hx]
      exact isUnit_iff_ne_zero.2 (hpow r hr)
    let ψ : (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) →+* ℂ := IsLocalization.lift (S := (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) hunit
    have hψB : ∀ b, ψ (algebraMap (MvPolynomial (Fin n) ℂ ⧸ Q) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) b) = PrimitiveElementFibres.evalAt Q x hx.1 b :=
      IsLocalization.lift_eq hunit
    have hψ : ψ.comp (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) = ev := by
      apply IsLocalization.ringHom_ext (Submonoid.powers a)
      refine RingHom.ext fun r => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, ← hsq, hψB, RingHom.comp_apply, hev]
      exact PrimitiveElementFibres.evalAt_projHom Q A hx r
    have hψx : ∀ j, ψ (xb j) = x j := fun j => by
      rw [hxb, hψB]
      simp [PrimitiveElementFibres.evalAt]
    obtain ⟨h1, h2, -⟩ := key ψ hψ
    have hψℓ : ψ ℓ = ∑ j, c j * x j := by rw [h2]; simp only [hψx]
    refine ⟨?_, fun j => ?_⟩
    · rw [← hmyroot, Polynomial.IsRoot, ← hψℓ, ← h1, (hdiv m).2 dvd_rfl, map_zero]
    · have hψr : ∀ r, ψ (algebraMap (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) r) = ev r := fun r => DFunLike.congr_fun hψ r
      have h3 := congrArg ψ (hQ' j)
      rw [h1, map_mul, hψr, hψx, hψℓ] at h3
      have hDy := congrArg ev hDs
      rw [map_mul, hev, hev] at hDy
      rw [Polynomial.map_mul, Polynomial.map_C, hnorm _ _ _ (htq j), Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_C, ← h3]
      simp only [map_mul, map_prod]
      rw [← hDy, ← Finset.mul_prod_erase Finset.univ (fun k => eval y (tq k : MvPolynomial (Fin d) ℂ)) (Finset.mem_univ j)]
      ring
  ·
    intro τ hτ
    rw [← hmyroot] at hτ
    have : Algebra.IsIntegral (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a))) := Algebra.IsIntegral.of_finite (Localization.Away a) (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))
    have hevs : Function.Surjective ev := fun z =>
      ⟨algebraMap (MvPolynomial (Fin d) ℂ) (Localization.Away a) (C z), by rw [hev, eval_C]⟩
    have hdiv' : ∀ p : Polynomial (Localization.Away a), Polynomial.aeval ℓ p = 0 → m ∣ p := fun p hp => (hdiv p).1 hp
    have hroot := exists_point_of_root (R' := (Localization.Away a)) (B' := (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ Q) (Submonoid.powers a)))) ℓ m
    obtain ⟨ψ, hψ, hψℓ⟩ := hroot hdiv' ev hevs τ hτ
    obtain ⟨-, h2, h3⟩ := key ψ hψ
    refine ⟨fun j => ψ (xb j), ⟨fun q hq => ?_, ?_⟩, ?_⟩
    · rw [← h3, Ideal.Quotient.eq_zero_iff_mem.2 hq, map_zero, map_zero]
    · funext i
      have h4 := hlin ψ hψ i
      rw [h3, FibreBound.eval_pullback, eval_X] at h4
      exact h4
    · rw [← h2, hψℓ]

end DominantPrimitiveFibres

end GroundTheory.Heights₂.Heights
