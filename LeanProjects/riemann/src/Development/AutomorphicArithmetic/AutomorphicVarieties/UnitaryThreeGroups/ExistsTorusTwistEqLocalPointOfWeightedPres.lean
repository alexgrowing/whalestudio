import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

open Polynomial in
private theorem pts_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have halg : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral
  have hmon : (minpoly ℚ_[l] x).Monic := minpoly.monic halg
  have hn : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [hn, spectralValue_le_one_iff hmon]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
    refine ⟨q, hqm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), ← Polynomial.eval₂_map, hq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[l] x

private theorem pts_unit {B K : Type} [CommRing B] [Field K] [Algebra B K] (hi : Function.Injective (algebraMap B K))
    (b : B) (h0 : algebraMap B K b ≠ 0) (h : IsIntegral B (algebraMap B K b)⁻¹) : IsUnit b := by
  classical
  obtain ⟨p, hpm, hp⟩ := h
  set y := (algebraMap B K b)⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero h0
  letI : Invertible y := invertibleOfNonzero hy0
  have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap B K) y p
  rw [hp, invOf_eq_inv, hy, inv_inv] at hrev
  have hq : Polynomial.eval₂ (algebraMap B K) (algebraMap B K b) p.reverse = 0 :=
    (mul_eq_zero.mp hrev).resolve_right (pow_ne_zero _ (inv_ne_zero h0))
  rw [Polynomial.eval₂_at_apply] at hq
  have hq' : Polynomial.eval b p.reverse = 0 := hi (by rw [hq, map_zero])
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := p.reverse)
  have he := congrArg (Polynomial.eval b) hr
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.coeff_zero_reverse, hpm.leadingCoeff, hq',
    Polynomial.eval_mul, Polynomial.eval_X] at he
  have h1 : b * -Polynomial.eval b r = 1 := by
    rw [mul_neg, ← he]
    ring
  exact ⟨⟨b, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩

private theorem automorphic_points_exist {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin)
    (s : W.σ) : W.z s ∈ maximalIdeal R := mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s)

private theorem pts_sur {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [Field K] [Algebra O K]
    (f : R →ₐ[O] K) (x : R) (h0 : f x ≠ 0) (h3 : IsIntegral O (f x)⁻¹) : IsUnit x := by
  classical
  have hu : IsUnit (⟨f x, AlgHom.mem_range_self f x⟩ : f.range) :=
    pts_unit (B := f.range) (K := K) (fun a b hab => Subtype.ext hab) _ h0 h3.tower_top
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 v.2
  have hfr : f x * f r = 1 := by
    rw [hr]
    exact congrArg Subtype.val hv
  by_contra hxu
  have hm : x * r ∈ maximalIdeal R := Ideal.mul_mem_right r _ hxu
  have hunit := (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (x * r) hm).map f
  rw [map_sub, map_one, map_mul, hfr, sub_self] at hunit
  exact not_isUnit_zero hunit

private theorem pts_loc {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsLocalRing R]
    (f : R →ₐ[c.O] PadicAlgCl l) : IsLocPt f := by
  intro x hx
  by_contra hge
  push_neg at hge
  have h0 : f x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hge
    linarith
  have hint : IsIntegral ℤ_[l] (f x)⁻¹ :=
    (pts_int _).mpr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hge)
  exact hx (pts_sur f x h0 hint.tower_top)

private theorem fg_lemma {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {K : Type} [Field K]
    [Algebra O K] (P : Submodule O A) (I : Ideal A) (ξ : A →ₐ[O] K) (hξ : ∀ a ∈ I, ξ a = 0)
    (h : (Submodule.map (Ideal.Quotient.mkₐ O I).toLinearMap P).FG) :
    (Submodule.map ξ.toLinearMap P).FG := by
  have he : ξ.toLinearMap = (Ideal.Quotient.liftₐ I ξ hξ).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ O I).toLinearMap := by
    ext a
    rfl
  rw [he, Submodule.map_comp]
  exact h.map _

set_option maxHeartbeats 1000000 in
theorem UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ ξ : W.A →ₐ[c.O] PadicAlgCl l, OnS (Ideal.span (Set.range g)) ξ →
            ∃ (t : (PadicAlgCl l)ˣ) (f : S →ₐ[c.O] PadicAlgCl l), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val) := by
  intro l _ c R S _ _ _ _ _ _ W h qh hqh κ g w hg hk hM ξ hOn
  have hfg : (Submodule.map ξ.toLinearMap (W.gr 0)).FG := fg_lemma (W.gr 0) _ ξ hOn hM
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  obtain ⟨hcomp, -, -, hinj, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hcomp
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.mk fun x =>
    ((IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).extendScalars hinj
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite c.O ℤ R W (automorphic_points_exist W h) (PadicAlgCl l) ξ hfg
  have hker : ∀ a ∈ RingHom.ker qh, Ξ a = 0 := by
    intro a ha
    rw [hk] at ha
    have hle : Ideal.span (Set.range fun i => (g i : R)) ≤ RingHom.ker Ξ := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h1 := congrArg (fun φ : W.A →ₐ[c.O] PadicAlgCl l => φ (g i)) hΞ
      simp only [AlgHom.comp_apply, Subalgebra.coe_val] at h1
      rw [h1, act_of_mem W.gr t ξ (hg i), hOn (g i) (Ideal.subset_span ⟨i, rfl⟩), mul_zero]
    exact RingHom.mem_ker.mp (hle ha)
  let f : S →ₐ[c.O] PadicAlgCl l := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hqh).symm.toAlgHom
  have hf : ∀ r, f (qh r) = Ξ r := by
    intro r
    have hmk : (Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r) =
        Ideal.Quotient.mk (RingHom.ker qh) r := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker
      ((Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r)) = Ξ r
    rw [hmk]
    rfl
  refine ⟨(zpowersHom (PadicAlgCl l)ˣ).symm t, f, pts_loc f, ?_⟩
  rw [show tz ((zpowersHom (PadicAlgCl l)ˣ).symm t) = t from Equiv.apply_symm_apply _ _, ← hΞ]
  refine AlgHom.ext fun a => ?_
  simp only [AlgHom.comp_apply, hf]
