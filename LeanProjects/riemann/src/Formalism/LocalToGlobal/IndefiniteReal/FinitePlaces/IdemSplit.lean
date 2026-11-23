import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCoreApprox
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DecompositionAlmostEverywhere

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem star_sqrt : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  rw [Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.MainNotions.UnusedSlot33.HK.conj_b]

theorem sqrt_sq : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
  have := D.host.sqd_sq
  rw [sq] at this; exact this

theorem idemAt_ne_zero {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  intro h0
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  apply (he.2 x hx0).1 hxP
  rw [h0, zero_mul, map_zero]; exact zero_mem _

theorem idemAt_int {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) :
    finPart D e ∈ intAE D := by
  have h := he.2 1 one_ne_zero
  have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have := not_not.1 (mt h.2 h1P)
  rwa [show ((1 : 𝓞 D.host.E) : D.host.E)⁻¹ = 1 by simp, map_one, mul_one] at this

set_option maxHeartbeats 800000 in

theorem decomp_AE (hadj : Algebra.adjoin D.host.F {D.host.sqrtMinusD} = ⊤) (z : AE D) :
    ∃ p q : AF D.host.F, z = algebraMap (AF D.host.F) (AE D) p +
      algebraMap (AF D.host.F) (AE D) q * incA D D.host.sqrtMinusD :=
  _root_.UpperTheory.Reformulated.B.DecompositionAlmostEverywhere.decomp_AE hadj z

theorem two_mul_eq_zero {z : AE D} (h : (2 : AE D) * z = 0) : z = 0 := by
  have h2 : algebraMap D.host.F (AE D) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AE D)) 2, ← map_mul]; norm_num; rfl
  calc z = algebraMap D.host.F (AE D) (1 / 2) * 2 * z := by rw [h2, one_mul]
    _ = 0 := by rw [mul_assoc, h, mul_zero]

theorem cA_alg (x : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) x) = algebraMap (AF D.host.F) (AE D) x := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (x ⊗ₜ[D.host.F] 1) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

set_option maxHeartbeats 800000 in

theorem fixed_AE (hadj : Algebra.adjoin D.host.F {D.host.sqrtMinusD} = ⊤) {z : AE D} (hz : cA D z = z) :
    ∃ r : AF D.host.F, z = algebraMap (AF D.host.F) (AE D) r := by
  obtain ⟨p, q, rfl⟩ := decomp_AE hadj z
  refine ⟨p, ?_⟩
  have hcu : cA D (incA D D.host.sqrtMinusD) = -incA D D.host.sqrtMinusD := by rw [cA_incA, star_sqrt, map_neg]
  have hcp : ∀ x : AF D.host.F, cA D (algebraMap (AF D.host.F) (AE D) x) = algebraMap (AF D.host.F) (AE D) x :=
    cA_alg
  rw [map_add, map_mul, hcp, hcp, hcu] at hz
  have h0 : (2 : AE D) * (algebraMap (AF D.host.F) (AE D) q * incA D D.host.sqrtMinusD) = 0 := by
    linear_combination -hz
  rw [two_mul_eq_zero h0, add_zero]

set_option synthInstance.maxHeartbeats 200000 in

theorem adjoin_top_of (b : D.host.E) (t N : D.host.F)
    (ht : algebraMap D.host.F D.host.E t = b + star b) (hN : algebraMap D.host.F D.host.E N = b * star b)
    (hb : star b ≠ b) : Algebra.adjoin D.host.F {b} = ⊤ := by
  have hbi : IsIntegral D.host.F b := Algebra.IsIntegral.isIntegral b
  have hq : aeval b (X ^ 2 - C t * X + C N : D.host.F[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, ht, hN]
    ring
  have hqm : (X ^ 2 - C t * X + C N : D.host.F[X]).Monic := by monicity!
  have hqd : (X ^ 2 - C t * X + C N : D.host.F[X]).natDegree = 2 := by compute_degree!
  have hnot : b ∉ (algebraMap D.host.F D.host.E).range := fun h => hb ((D.sp.cm.fixed b).2 h)
  have hmin : minpoly D.host.F b = X ^ 2 - C t * X + C N := by
    have hdvd := minpoly.dvd D.host.F b hq
    have h1 : (minpoly D.host.F b).natDegree ≠ 1 := fun h => hnot (minpoly.natDegree_eq_one_iff.1 h)
    have h0 : 0 < (minpoly D.host.F b).natDegree := minpoly.natDegree_pos hbi
    have hle : (minpoly D.host.F b).natDegree ≤ 2 := by
      rw [← hqd]; exact natDegree_le_of_dvd hdvd hqm.ne_zero
    exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hbi) hqm hdvd (by omega)).symm
  have htop : IntermediateField.adjoin D.host.F {b} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.adjoin.finrank hbi, IntermediateField.finrank_top', hmin, hqd, D.sp.cm.deg2]
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hbi.isAlgebraic, htop,
    IntermediateField.top_toSubalgebra]

set_option maxHeartbeats 800000 in

theorem approx_int (v : HeightOneSpectrum (𝓞 D.host.F)) (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    ∃ y : 𝓞 D.host.E, Valued.v (compV v ι z - ι (y : D.host.E)) < 1 ∧
      Valued.v (compV v ι (cF D z) - ι (star (y : D.host.E))) < 1 := by
  obtain ⟨n, hnv, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hnl : v.intValuation n < 1 := (HeightOneSpectrum.intValuation_lt_one_iff_mem v n).2 hnv
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Formalism.L2.S.Pv.PsiTrCore.exists_approx a (fun w => ha w) n hn0
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b * y, ?_, ?_⟩
    · rw [compV, Algebra.TensorProduct.lift_tmul]
      have : ι ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b * y : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F (v.adicCompletion D.host.F) (b : D.host.F) * ι (y : D.host.E) := by
        show ι ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : D.host.E) * (y : D.host.E)) = _
        rw [algebraMap_O (D := D) b, map_mul, AlgHom.commutes]
      rw [this, ← sub_mul, Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (val_emb_le v ι y)) (lt_of_le_of_lt (hb v) hnl)
    · show Valued.v (compV v ι (a ⊗ₜ[D.host.F] star (y : D.host.E)) - _) < 1
      rw [compV, Algebra.TensorProduct.lift_tmul]
      have : ι (star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b * y : 𝓞 D.host.E) : D.host.E)) =
          algebraMap D.host.F (v.adicCompletion D.host.F) (b : D.host.F) * ι (starO y : D.host.E) := by
        show ι (star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) b : D.host.E) * (y : D.host.E))) = _
        rw [algebraMap_O (D := D) b, star_mul, mul_comm, map_mul, coe_starO,
          show star (algebraMap D.host.F D.host.E (b : D.host.F)) = algebraMap D.host.F D.host.E (b : D.host.F) from
          (D.sp.cm.fixed _).2 ⟨_, rfl⟩, AlgHom.commutes]
      rw [this, ← coe_starO, ← sub_mul, Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (val_emb_le v ι (starO y))) (lt_of_le_of_lt (hb v) hnl)
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero, show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, sub_zero, Valuation.map_zero]
      exact zero_lt_one
    · rw [map_zero, map_zero, show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, star_zero, map_zero, sub_zero,
        Valuation.map_zero]
      exact zero_lt_one
  | add x y _ _ hx hy =>
    obtain ⟨a, ha1, ha2⟩ := hx
    obtain ⟨b, hb1, hb2⟩ := hy
    refine ⟨a + b, ?_, ?_⟩
    · rw [show ((a + b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) + (b : D.host.E) from rfl, map_add, map_add,
        show compV v ι x + compV v ι y - (ι (a : D.host.E) + ι (b : D.host.E)) =
        (compV v ι x - ι (a : D.host.E)) + (compV v ι y - ι (b : D.host.E)) by ring]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha1 hb1)
    · rw [show ((a + b : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) + (b : D.host.E) from rfl, map_add, map_add,
        star_add, map_add, show compV v ι (cF D x) + compV v ι (cF D y) -
        (ι (star (a : D.host.E)) + ι (star (b : D.host.E))) = (compV v ι (cF D x) - ι (star (a : D.host.E))) +
        (compV v ι (cF D y) - ι (star (b : D.host.E))) by ring]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha2 hb2)
  | neg x _ hx =>
    obtain ⟨a, ha1, ha2⟩ := hx
    refine ⟨-a, ?_, ?_⟩
    · rw [show ((-a : 𝓞 D.host.E) : D.host.E) = -(a : D.host.E) from rfl, map_neg, map_neg,
        show -compV v ι x - -ι (a : D.host.E) = -(compV v ι x - ι (a : D.host.E)) by ring, Valuation.map_neg]
      exact ha1
    · rw [show ((-a : 𝓞 D.host.E) : D.host.E) = -(a : D.host.E) from rfl, map_neg, map_neg, star_neg, map_neg,
        show -compV v ι (cF D x) - -ι (star (a : D.host.E)) = -(compV v ι (cF D x) - ι (star (a : D.host.E))) by ring,
        Valuation.map_neg]
      exact ha2

set_option maxHeartbeats 1000000 in

theorem idemAt_split {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) :
    ¬ Lev.IsConjPl (D := D) P P := by
  intro hc
  obtain ⟨w, hw⟩ : ∃ w, w = belowPl P := ⟨_, rfl⟩
  have hs := below_of_idemAt he
  rw [← hw] at hs
  have h1 := he.1.1
  have h2 := he.1.2.1
  have hint := idemAt_int he
  have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, h1]

  obtain ⟨u, hu0⟩ : ∃ u : AE D, u = incA D D.host.sqrtMinusD := ⟨_, rfl⟩
  have hadj0 : star D.host.sqrtMinusD ≠ D.host.sqrtMinusD := by
    rw [star_sqrt]; intro h
    have : D.host.sqrtMinusD = 0 := by linear_combination -h / 2
    exact Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero D.host this
  have ht0 : algebraMap D.host.F D.host.E 0 = D.host.sqrtMinusD + star D.host.sqrtMinusD := by rw [star_sqrt]; simp
  have hN0 : algebraMap D.host.F D.host.E (D.host.d : D.host.F) = D.host.sqrtMinusD * star D.host.sqrtMinusD := by
    rw [star_sqrt, mul_neg, sqrt_sq, neg_neg, map_natCast]
  have hadj := adjoin_top_of D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) := by
    intro x y h
    apply Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (FaithfulSMul.algebraMap_injective D.host.F D.host.E)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply] at h
    exact h
  obtain ⟨a, ha0⟩ : ∃ a : AE D, a = e - cA D e := ⟨_, rfl⟩
  have hca : cA D a = -a := by rw [ha0, map_sub, cA_cA]; ring
  have hcu : cA D u = -u := by rw [hu0, cA_incA, star_sqrt, map_neg]
  obtain ⟨r, hr⟩ := fixed_AE hadj (z := a * u) (by rw [map_mul, hca, hcu]; ring)
  have haa : a * a = phiE w 1 := by
    rw [ha0, ← hs]; linear_combination h1 + hcc - 2 * h2
  have hu2 : u * u = algebraMap D.host.F (AE D) (-(D.host.d : D.host.F)) := by
    rw [hu0, ← map_mul, sqrt_sq, show -(D.host.d : D.host.E) = algebraMap D.host.F D.host.E (-(D.host.d : D.host.F)) by simp,
      incA_alg]
  have hceps : cA D e * phiE w 1 = cA D e := by
    have := congrArg (cA D) heps; rwa [map_mul, cA_phiE] at this
  have haeps : a * phiE w 1 = a := by rw [ha0, sub_mul, heps, hceps]
  have hrr : r * r = sA w (algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) * 1) := by
    apply hinj
    calc algebraMap (AF D.host.F) (AE D) (r * r) = (a * u) * (a * u) := by rw [map_mul, ← hr]
      _ = (a * a) * (u * u) := by ring
      _ = algebraMap D.host.F (AE D) (-(D.host.d : D.host.F)) * phiE w 1 := by rw [haa, hu2]; ring
      _ = phiE w (algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) * 1) := phiE_smul w _ 1
  obtain ⟨s, hsdef⟩ : ∃ s, s = evalV D.host.F w (sndA D.host.F r) := ⟨_, rfl⟩
  have hss : s * s = algebraMap D.host.F (w.adicCompletion D.host.F) (-(D.host.d : D.host.F)) := by
    have := congrArg (fun x : AF D.host.F => evalV D.host.F w (sndA D.host.F x)) hrr
    simp only [map_mul, mul_one] at this
    rw [hsdef]; exact this.trans (sglV_same w _)
  have hrs : r = sA w s := by
    have h : algebraMap (AF D.host.F) (AE D) r = algebraMap (AF D.host.F) (AE D) (sA w 1 * r) := by
      rw [map_mul, ← hr]
      show a * u = phiE w 1 * (a * u)
      rw [← mul_assoc, mul_comm (phiE w 1) a, haeps]
    rw [hinj h, sA_one_mul, hsdef]
  have hroot : s ^ 2 - ((0 : D.host.F) : w.adicCompletion D.host.F) * s +
      ((D.host.d : D.host.F) : w.adicCompletion D.host.F) = 0 := by
    rw [← algebraMap_adic_eq, ← algebraMap_adic_eq, map_zero, sq, hss, map_neg]; ring
  obtain ⟨ι, hι, -⟩ := emb_exists w D.host.sqrtMinusD 0 (D.host.d : D.host.F) ht0 hN0 hadj0 s hroot
  have hau : (e - cA D e) * u = phiE w s := by rw [← ha0, hr, hrs]; rfl
  have heu : e * u = e * phiE w s := by
    have h2' : (2 : AE D) * (e * u - e * phiE w s) = 0 := by
      linear_combination (-2 * u) * h1 + (2 * u) * h2 + (2 * e) * hau
    exact sub_eq_zero.1 (two_mul_eq_zero h2')
  have hid : ∀ y : D.host.E, e * incA D y = e * phiE w (ι y) := by
    intro y
    have hy : y ∈ Algebra.adjoin D.host.F {D.host.sqrtMinusD} := by rw [hadj]; exact Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      rw [← hu0, hι]; exact heu
    | algebraMap f =>
      rw [incA_alg, AlgHom.commutes]
      calc e * algebraMap D.host.F (AE D) f = (e * phiE w 1) * algebraMap D.host.F (AE D) f := by rw [heps]
        _ = e * phiE w (algebraMap D.host.F (w.adicCompletion D.host.F) f * 1) := by
          rw [mul_assoc, mul_comm (phiE w 1), phiE_smul]
        _ = _ := by rw [mul_one]
    | add x y _ _ hx hy => rw [map_add, mul_add, hx, hy, map_add, phiE_add, mul_add]
    | mul x y _ _ hx hy =>
      calc e * incA D (x * y) = (e * incA D x) * incA D y := by rw [map_mul, mul_assoc]
        _ = (e * phiE w (ι x)) * incA D y := by rw [hx]
        _ = (e * incA D y) * phiE w (ι x) := by ring
        _ = (e * phiE w (ι y)) * phiE w (ι x) := by rw [hy]
        _ = e * phiE w (ι (x * y)) := by rw [map_mul ι, phiE_mul]; ring
  have hz := mul_e_of w e ι hid heps
  have hk : compV w ι (finPart D e) = 1 := by
    have hee := hz e
    rw [h1] at hee
    have hk2 : compV w ι (finPart D e) = compV w ι (finPart D e) * compV w ι (finPart D e) := by
      have := congrArg (fun x => compV w ι (finPart D x)) hee
      simp only [map_mul, compV_phiE] at this
      exact this
    rcases mul_eq_zero.1 (show compV w ι (finPart D e) * (compV w ι (finPart D e) - 1) = 0 by
      linear_combination -hk2) with h0 | h0
    · exfalso; apply idemAt_ne_zero he
      rw [hee, h0, phiE_zero, mul_zero]
    · linear_combination h0
  have hkc : compV w ι (finPart D (cA D e)) = 0 := by
    have := congrArg (fun x => compV w ι (finPart D x)) hs
    simp only [map_add, compV_phiE, hk] at this
    linear_combination this
  have hP_iff : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ Valued.v (ι (x : D.host.E)) < 1) := by
    intro x hx0
    have hxE : (x : D.host.E) ≠ 0 := by exact_mod_cast hx0
    have hιx : ι (x : D.host.E) ≠ 0 := (map_ne_zero ι).2 hxE
    have hne : Valued.v (ι (x : D.host.E)) ≠ 0 := (Valuation.ne_zero_iff _).2 hιx
    rw [he.2 x hx0, hid, map_inv₀]
    constructor
    · intro hn
      by_contra hge
      push Not at hge
      apply hn
      have hc1 : Valued.v (ι (x : D.host.E))⁻¹ ≤ 1 := by
        rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge
      rw [map_mul, finPart_phiE]
      exact intAE_mul hint (AddSubgroup.subset_closure ⟨sglV w (ι (x : D.host.E))⁻¹,
        sglV_int w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ w).2 hc1), 1, by simp⟩)
    · intro hlt hmem
      have h1' := compV_int w ι hmem
      rw [map_mul, map_mul, hk, one_mul, compV_phiE, map_inv₀] at h1'
      have h5 := mul_le_mul' h1' (le_refl (Valued.v (ι (x : D.host.E))))
      rw [inv_mul_cancel₀ hne, one_mul] at h5
      exact absurd hlt (not_lt.2 h5)
  obtain ⟨y, hy1, hy2⟩ := approx_int w ι hint
  rw [hk, ← finPart_cA, hkc, zero_sub, Valuation.map_neg] at *
  have hyv : Valued.v (ι (y : D.host.E)) = 1 := by
    have : Valued.v (1 - ι (y : D.host.E)) < Valued.v (1 : w.adicCompletion D.host.F) := by rw [Valuation.map_one]; exact hy1
    have h' := Valuation.map_sub_eq_of_lt_left (Valued.v) this
    rw [Valuation.map_one] at h'
    rw [← h', sub_sub_cancel]
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hyv; simp at hyv
  have hsy0 : starO y ≠ 0 := by
    intro h; apply hy0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    have : star ((y : 𝓞 D.host.E) : D.host.E) = 0 := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simpa using this
  have hsP : starO y ∈ P.asIdeal := (hP_iff (starO y) hsy0).2 hy2
  obtain ⟨c, hcP, hce⟩ := hc _ hsP
  have : c = y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    show (c : D.host.E) = y
    rw [hce, coe_starO, star_star]
  rw [this] at hcP
  have := (hP_iff y hy0).1 hcP
  rw [hyv] at this
  exact lt_irrefl _ this

end Formalism.IndefR.Fin

end
