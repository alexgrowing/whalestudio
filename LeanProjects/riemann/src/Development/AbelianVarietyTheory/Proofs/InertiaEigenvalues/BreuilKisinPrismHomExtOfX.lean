import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

theorem hom_ext_of_hf_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
    (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  intro l _ K bk C g g' hX

  have hI : ∀ x : bk.S, BK.hf g x - BK.hf g' x ∈ C.I := by
    intro x
    have hr : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
      (bk.str.apply_symm_apply _).symm
    have h1 := g.f_str _ x hr
    have h2 := g'.f_str _ x hr
    exact Ideal.Quotient.eq.1 (h1.trans h2.symm)
  have hH : IsHausdorff (JJ C) C.A := C.complete.toIsHausdorff

  have hCC : (BK.hf g).comp (PowerSeries.C (R := Wq l bk.a)) = (BK.hf g').comp PowerSeries.C :=
    GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) C.A (JJ C) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hH _ _
      (fun w => Ideal.mem_sup_right (hI _))

  have hP : ∀ p : Polynomial (Wq l bk.a), BK.hf g (p : bk.S) = BK.hf g' (p : bk.S) := by
    have h := Polynomial.ringHom_ext (f := (BK.hf g).comp (Polynomial.coeToPowerSeries.ringHom))
      (g := (BK.hf g').comp Polynomial.coeToPowerSeries.ringHom)
      (fun a => by
        simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
        exact RingHom.congr_fun hCC a)
      (by simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]; exact hX)
    intro p
    exact RingHom.congr_fun h p

  have hXe : ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
    have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
      · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
      · rw [if_pos h, h, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hd
    refine ⟨(q : bk.S), ?_⟩
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C, map_natCast] at h
    show _ = (bk.Ep : bk.S) - _
    linear_combination -h
  obtain ⟨q, hq⟩ := hXe
  have hgXe : BK.hf g X ^ bk.Ep.natDegree ∈ JJ C := by
    rw [← map_pow, hq, map_sub, map_mul, map_natCast]
    refine Ideal.sub_mem _ (Ideal.mem_sup_right (g.f_I _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

  have hsplit : ∀ (N : ℕ) (f : bk.S), ∃ (p : Polynomial (Wq l bk.a)) (h : bk.S), f = (p : bk.S) + X ^ N * h := by
    intro N f
    obtain ⟨h, hh⟩ := (PowerSeries.X_pow_dvd_iff (n := N)
      (φ := f - ((trunc N f : Polynomial (Wq l bk.a)) : bk.S))).2 (fun m hm => by
        rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self])
    exact ⟨_, h, by rw [← hh]; ring⟩
  apply Hom.ext'
  refine RingHom.ext fun f => ?_
  change BK.hf g f = BK.hf g' f
  have key : ∀ n : ℕ, BK.hf g f - BK.hf g' f ∈ JJ C ^ n := by
    intro n
    obtain ⟨p, h, hh⟩ := hsplit (bk.Ep.natDegree * n) f
    have e : ∀ φ : bk.S →+* C.A, φ f = φ (p : bk.S) + φ X ^ (bk.Ep.natDegree * n) * φ h := fun φ => by
      have := congrArg φ hh
      rwa [map_add, map_mul, map_pow] at this
    have hm : BK.hf g X ^ (bk.Ep.natDegree * n) ∈ JJ C ^ n := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hgXe n
    have e2 : BK.hf g f - BK.hf g' f = BK.hf g X ^ (bk.Ep.natDegree * n) * (BK.hf g h - BK.hf g' h) := by
      have hXN : BK.hf g' X ^ (bk.Ep.natDegree * n) = BK.hf g X ^ (bk.Ep.natDegree * n) := by rw [hX]
      linear_combination e (BK.hf g) - e (BK.hf g') + hP p - BK.hf g' h * hXN
    rw [e2]
    exact Ideal.mul_mem_right _ _ hm
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP.BK
