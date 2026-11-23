import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPowStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ApproxRoot

theorem mul_eval_derivative_scaleRoots {R : Type} [CommRing R] (p : Polynomial R) (s r : R) :
    s * (Polynomial.derivative (p.scaleRoots s)).eval (s * r) =
      s ^ p.natDegree * (Polynomial.derivative p).eval r := by
  have h : (p.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ p.natDegree * p := by
    have := Polynomial.scaleRoots_eval₂_mul (p := p) Polynomial.C Polynomial.X s
    rwa [Polynomial.eval₂_C_X] at this
  rw [← map_pow] at h
  have h2 := congrArg (fun t => (Polynomial.derivative t).eval r) h
  simp only [Polynomial.derivative_C_mul] at h2
  simpa [Polynomial.derivative_comp, Polynomial.eval_comp] using h2

theorem sub_mem_pow {R : Type} [CommRing R] (I : Ideal R) (P : Polynomial R) (s r x : R) (n : ℕ) (hs : IsUnit s)
    (hr : P.eval r = 0) (hd : IsUnit ((Polynomial.derivative P).eval r))
    (hx : (P.scaleRoots s).eval x ∈ I ^ n) (hxy : x - s * r ∈ I) : x - s * r ∈ I ^ n := by
  have hy : (P.scaleRoots s).eval (s * r) ∈ I ^ n := by
    rw [Polynomial.scaleRoots_eval_mul, hr, mul_zero]
    exact zero_mem _
  have h := GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow R I (P.scaleRoots s) (s * r) x s (s ^ P.natDegree * (Polynomial.derivative P).eval r) n
    hy hx (by rw [← neg_sub]; exact neg_mem hxy)
    (by rw [mul_eval_derivative_scaleRoots, sub_self]; exact zero_mem _)
  rw [Ideal.unit_mul_mem_iff_mem _ (((hs.pow _).mul hd).pow n)] at h
  rw [← neg_sub]
  exact neg_mem h

end GlobalTheory.BSP.ApproxRoot

open GlobalTheory.BSP.ApproxRoot in

theorem GlobalTheory.BSP.approxRoot_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → aDp l (bk.ev q) - (l : Per.BdRp l) ^ m * C.o (((bk.str.symm (Ideal.Quotient.mk _ X) : ↥(OL K)) : ↥K.1) : Om l) ∈ Per.FilP l n := by
  intro l _ K bk C n m q hq hroot
  obtain ⟨hfil, -⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := thetaD_props l
  let e : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev
  let f : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a)
  let g : bk.S →+* Per.BdRp l := C.o.comp ((K.1.val : ↥K.1 →+* Om l).comp (((OL K).val : ↥(OL K) →+* ↥K.1).comp
    (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk _))))
  have hg : ∀ s, g s = C.o (((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) := fun _ => rfl
  have hθ : ∀ s : bk.S, ((Per.θ l (bk.ev s) : OC l) : ℂ_[l]) =
      ((((bk.str.symm (Ideal.Quotient.mk _ s) : ↥(OL K)) : ↥K.1) : Om l) : ℂ_[l]) := fun s => by
    rw [bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s)) s (bk.str.apply_symm_apply _).symm, coe_intToOC]
  have hef : e.comp PowerSeries.C = f := RingHom.ext fun w => congrArg (aDp l) (bk.ev_C w)
  have hgf : g.comp PowerSeries.C = f := RingHom.ext fun w =>
    GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w _ (by rw [← bk.ev_C]; exact hθ _)
  have hgE : g bk.E = 0 := by
    rw [hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    simp
  have hθeg : ∀ s, Per.θD l (e s) = Per.θD l (g s) := fun s => by
    rw [hg, C.o_sec.th]
    exact (hth _).trans (hθ s)
  have hl : IsUnit ((l : Per.BdRp l) ^ m) := (isUnit_l_BdRp l).pow m
  have hr : (bk.Ep.map f).eval (g X) = 0 := by
    rw [Polynomial.eval_map, ← hgf, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe]
    exact hgE
  have hd : IsUnit ((Polynomial.derivative (bk.Ep.map f)).eval (g X)) := by
    obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
    have h := congrArg (fun t => (Polynomial.map f t).eval (g X)) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.eval_add, Polynomial.eval_mul, hr, mul_zero,
      zero_add, Polynomial.map_C, Polynomial.eval_C, map_pow f, map_natCast f] at h
    rw [Polynomial.derivative_map]
    exact isUnit_of_mul_isUnit_right (h ▸ (isUnit_l_BdRp l).pow c)
  haveI : Nontrivial (Per.BdRp l) := (Per.θD l).domain_nontrivial
  have hx : ((bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m)).eval (e q) ∈ Ideal.span {e bk.E} ^ n := by
    have h1 : (bk.Ep.map f).scaleRoots ((l : Per.BdRp l) ^ m) =
        (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)).map f := by
      rw [Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero), map_pow,
        map_natCast]
    rw [h1, Polynomial.eval_map, ← hef, ← Polynomial.hom_eval₂, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← map_pow]
    exact map_dvd e hroot
  have hxy : e q - (l : Per.BdRp l) ^ m * g X ∈ Ideal.span {e bk.E} := by
    have h1 : e q - (l : Per.BdRp l) ^ m * g X ∈ Per.FilP l 1 := by
      rw [← hker, map_sub, hθeg, ← map_sub]
      obtain ⟨t, ht⟩ := hq
      have h2 := congrArg g ht
      rw [map_sub, map_mul, map_pow, map_natCast, map_mul, hgE, zero_mul] at h2
      rw [h2, map_zero]
    rwa [hfil, pow_one] at h1
  have h := sub_mem_pow _ _ _ _ _ n hl hr hd hx hxy
  rw [Ideal.span_singleton_pow] at h
  rw [hfil]
  exact h
