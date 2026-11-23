import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.OEStable

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem eq_zero_of_forall_dvd (z : WCb l) (h : ∀ n, ((l : ℕ) : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

private theorem sigmaA_eq_map_pt (g : GQ l) (a : Ainf l) : Per.σA g a = WittVector.map (Per.σF g) a := by
  apply GlobalTheory.Prism.inclW_injective
  rw [← galW_inclW]
  exact WittVector.ext fun n => autCb_alg l (galTilt l g) (a.coeff n)

variable {K : FinExt l} (bk : BK K)

theorem sat (w : WCb l) (hw : ((l : ℕ) : WCb l) * w ∈ bk.OE) : w ∈ bk.OE := by
  haveI := perfect_Cb (l := l)
  obtain ⟨ek, pr, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  intro n
  obtain ⟨m, s, y, h⟩ := hw (n + 1)
  have h0 : (bk.evW s).coeff 0 = 0 := by
    have e : bk.evW s = (bk.evW X ^ m * w - ((l : ℕ) : WCb l) ^ n * y) * ((l : ℕ) : WCb l) := by
      linear_combination -h
    rw [e, WittVector.mul_charP_coeff_zero]
  have h1 : (bk.ev s).coeff 0 = 0 := by
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := WittVector.map_coeff _ _ _
    rw [e] at h0
    exact IsFractionRing.injective (OCb l) (Cb l) (h0.trans (map_zero _).symm)
  have h2 : PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s = 0 :=
    hinj (by rw [hek, h1, map_zero])
  have h3 : ∀ i, ∃ c : Wq l bk.a, coeff i s = ((l : ℕ) : Wq l bk.a) * c := fun i => by
    have h4 := congrArg (coeff i) h2
    rw [coeff_map, map_zero] at h4
    have h5 : coeff i s ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) := h4
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h5
    exact h5
  choose c hc using h3
  have h5 : s = ((l : ℕ) : bk.S) * PowerSeries.mk c := by
    ext i
    rw [hc, ← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, coeff_mk]
  refine ⟨m, PowerSeries.mk c, y, ?_⟩
  apply sub_eq_zero.1
  apply WittVector.eq_zero_of_p_mul_eq_zero
  rw [h5, map_mul, map_natCast] at h
  linear_combination h

theorem closed (w : WCb l) (h : ∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) : w ∈ bk.OE := by
  intro n
  obtain ⟨v, hv, z, hz⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hv n
  exact ⟨m, s, y + bk.evW X ^ m * z, by linear_combination hy + bk.evW X ^ m * hz⟩

theorem frob (w : WCb l) (hw : w ∈ bk.OE) : frobW l w ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have key : ∀ t : bk.S, frobW l (bk.evW t) = bk.evW (frobS l bk.a t) := fun t => by
    rw [BK.evW, RingHom.comp_apply, RingHom.comp_apply, frobW_inclW, bk.ev_frob]
  refine ⟨l * m, frobS l bk.a s, frobW l y, ?_⟩
  have h' := congrArg (frobW l) h
  simp only [map_mul, map_add, map_pow, map_natCast, key, frobS_X] at h'
  rw [pow_mul]
  linear_combination h'

theorem gal (g : ↥(GK K)) (hg : bk.FixFlat g) (w : WCb l) (hw : w ∈ bk.OE) : galW l (g : GQ l) w = w := by
  obtain ⟨-, -, -, hflat, -, hcomp, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  haveI := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l (OCb l) bk.flat hflat hcomp).1
  have hteich : Per.σA (g : GQ l) (WittVector.teichmuller l bk.flat) = WittVector.teichmuller l bk.flat := by
    rw [sigmaA_eq_map_pt, WittVector.map_teichmuller]
    exact congrArg _ hg
  have hfix : (Per.σA (g : GQ l)).comp bk.ev = bk.ev := by
    refine ringHom_ext_of_sep _ _ (fun r => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bk.ev_C, bk.gal_w]
    · rw [RingHom.comp_apply, bk.ev_X, hteich]
    · intro x hx
      rw [RingHom.comp_apply, bk.ev_X, hteich] at hx
      refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l bk.flat}) x fun n => ?_
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hx n
  have hW : ∀ t : bk.S, galW l (g : GQ l) (bk.evW t) = bk.evW t := fun t => by
    change galW l _ (inclW l (bk.ev t)) = inclW l (bk.ev t)
    rw [galW_inclW, ← RingHom.comp_apply (Per.σA _) bk.ev, hfix]
  obtain ⟨-, -, hu, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  apply sub_eq_zero.1
  apply eq_zero_of_forall_dvd
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have h' := congrArg (galW l (g : GQ l)) h
  simp only [map_mul, map_add, map_pow, map_natCast, hW] at h'
  obtain ⟨u, hu'⟩ := hu.pow m
  have e : (u : WCb l) * (galW l (g : GQ l) w - w) =
      ((l : ℕ) : WCb l) ^ n * (galW l (g : GQ l) y - y) := by
    rw [hu']; linear_combination h' - h
  refine ⟨(↑u⁻¹ : WCb l) * (galW l (g : GQ l) y - y), ?_⟩
  calc galW l (g : GQ l) w - w = (↑u⁻¹ : WCb l) * ((u : WCb l) * (galW l (g : GQ l) w - w)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [e]; ring

theorem inv (w : WCb l) (hw : w ∈ bk.OE) (hu : IsUnit w) : ∃ w' ∈ bk.OE, w * w' = 1 := by
  haveI := perfect_Cb (l := l)
  obtain ⟨-, -, -, -, hinv⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨u, rfl⟩ := hu
  have hy : WittVector.constantCoeff (p := l) (R := Cb l) u ∈
      bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := Subring.mem_map.2 ⟨u, hw, rfl⟩
  obtain ⟨v, hv, hvy⟩ := Subring.mem_map.1 (hinv _ hy)
  have hne : WittVector.constantCoeff (p := l) (R := Cb l) u ≠ 0 := by
    intro h0
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  have h1 : (u : WCb l) * v - 1 ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hvy, map_one, mul_inv_cancel₀ hne, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : z ∈ bk.OE := sat bk z (by
    rw [← hz]; exact sub_mem (mul_mem hw hv) (one_mem _))
  have huv : (u : WCb l) * v = 1 - (-((l : ℕ) : WCb l) * z) := by linear_combination hz
  have hi : (↑u⁻¹ : WCb l) * u = 1 := Units.inv_mul u
  refine ⟨↑u⁻¹, closed bk _ fun n => ⟨v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i,
    mul_mem hv (sum_mem fun i _ => pow_mem (mul_mem (neg_mem (natCast_mem _ l)) hz') i),
    ⟨(↑u⁻¹ : WCb l) * (-z) ^ n, ?_⟩⟩, u.mul_inv⟩
  have hgeom := geom_sum_mul_neg (-((l : ℕ) : WCb l) * z) n
  have hq : (-((l : ℕ) : WCb l) * z) ^ n = ((l : ℕ) : WCb l) ^ n * (-z) ^ n := by
    rw [neg_mul, ← mul_neg, mul_pow]
  linear_combination (-(↑u⁻¹ : WCb l)) * hgeom - ((↑u⁻¹ : WCb l) * ∑ i ∈ Finset.range n,
    (-((l : ℕ) : WCb l) * z) ^ i) * huv + (v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i) * hi
    - (↑u⁻¹ : WCb l) * hq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  intro l _ K bk
  exact ⟨sat bk, closed bk, frob bk, fun g hg w hw => gal bk g hg w hw, inv bk⟩

end GlobalTheory.OEStable
