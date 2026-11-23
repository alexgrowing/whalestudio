import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinApproxRootImageIndep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfPropertiesStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.InvLift

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ)

def InvSet : Subring bk.S where
  carrier := {x | ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev x) - bk.ev x}
  zero_mem' g := by simp
  one_mem' g := by simp
  neg_mem' {x} hx g := by
    have := (hx g).neg_right
    simpa [map_neg, neg_sub, sub_eq_add_neg, add_comm] using this
  add_mem' {x y} hx hy g := by
    have h := dvd_add (hx g) (hy g)
    rw [map_add, map_add]
    convert h using 1
    ring
  mul_mem' {x y} hx hy g := by
    have h := dvd_add (dvd_mul_of_dvd_right (hy g) (Per.σA (g : GQ l) (bk.ev x)))
      (dvd_mul_of_dvd_left (hx g) (bk.ev y))
    rw [map_mul, map_mul]
    convert h using 1
    ring

theorem C_mem (w : Wq l bk.a) : (C w : bk.S) ∈ InvSet bk m := fun g => by
  rw [bk.ev_C, bk.gal_w, sub_self]
  exact dvd_zero _

omit hl in
theorem coe_sum_fin {R : Type} [CommRing R] {e : ℕ} (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem exists_div (s : bk.S) : ∃ (q : bk.S) (c : Fin bk.Ep.natDegree → Wq l bk.a),
    s = bk.E * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l (k := Fq l bk.a)).not_isUnit
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod s
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div s, fun i => ((hdist.isWeierstrassDivisorAt hI).mod s).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : bk.Ep.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (bk.Ep : (Wq l bk.a)⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

variable {bk m} in
theorem cancel_pow_l (k : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).1
    apply ih
    rwa [pow_succ, mul_assoc] at h

end GlobalTheory.BSP.InvLift

open GlobalTheory.BSP.InvLift in

theorem GlobalTheory.BSP.BK.exists_inv_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  intro l hl K bk m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.BSP.BK.exists_approx_root l K bk m
  have hqinv : q ∈ InvSet bk m := fun g => by
    obtain ⟨k, hk⟩ := GlobalTheory.BSP.approx_root_indep l K bk m M q hq1 hq2 (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    change bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * (bk.ev q - Per.σA (g : GQ l) (bk.ev q)) at hk
    rw [← neg_sub]
    exact (cancel_pow_l k _ hk).neg_right
  set e := bk.Ep.natDegree
  refine ⟨M * e, fun s => ?_⟩
  obtain ⟨q', c, hs⟩ := exists_div bk s
  refine ⟨∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ), ?_, fun g => ?_⟩
  · have key : ∀ i : Fin e, bk.E ∣ C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
        (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)) := by
      intro i
      have h1 : (l : bk.S) ^ (M * e) * X ^ (i : ℕ) = (l : bk.S) ^ (M * (e - i)) * ((l : bk.S) ^ M * X) ^ (i : ℕ) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, ← Nat.mul_add]
        congr 3
        have := i.2
        omega
      rw [mul_left_comm, h1]
      have := (hq1.trans (sub_dvd_pow_sub_pow q ((l : bk.S) ^ M * X) i)).mul_left (C (c i) * (l : bk.S) ^ (M * (e - i)))
      convert this using 1
      ring
    have heq : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) - (l : bk.S) ^ (M * e) * s =
        (∑ i : Fin e, (C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
          (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)))) - bk.E * ((l : bk.S) ^ (M * e) * q') := by
      rw [hs, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_sub (Finset.dvd_sum fun i _ => key i) (dvd_mul_right _ _)
  · have hmem : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) ∈ InvSet bk m :=
      Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Subring.mul_mem _ (C_mem bk m _)
        (Subring.pow_mem _ (natCast_mem _ _) _)) (Subring.pow_mem _ hqinv _)
    exact hmem g
