import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOneStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

theorem sep_complete_of_coord {R A B I : Type} [AddCommGroup R] [CommRing A] [CommRing B]
    (φ : I → R →+ B) (j : A →+* B) (hj : Function.Injective j) (t : A)
    (hs : ∀ c : I → A, ∃ x : R, ∀ i, φ i x = j (c i))
    (h1 : ∀ x : A, (∀ m : ℕ, t ^ m ∣ x) → x = 0)
    (h2 : ∀ a : ℕ → A, ∃ x : A, ∀ m : ℕ, t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i) :
    (∀ x : R, (∀ (m : ℕ) i, ∃ c, φ i x = j (t ^ m * c)) → ∀ i, φ i x = 0) ∧
    ∀ (k : ℕ) (f : ℕ → R), (∀ n i, ∃ c, φ i (f n) = j (t ^ (n + k) * c)) →
      ∃ x, ∀ (m : ℕ) i, ∃ c, φ i (x - ∑ n ∈ Finset.range m, f n) = j (t ^ (m + k) * c) := by
  refine ⟨fun x hx i => ?_, fun k f hf => ?_⟩
  · obtain ⟨y, hy⟩ := hx 0 i
    rw [pow_zero, one_mul] at hy
    have hdiv : ∀ m : ℕ, t ^ m ∣ y := by
      intro m
      obtain ⟨c, hc⟩ := hx m i
      exact ⟨c, hj (hy.symm.trans hc)⟩
    rw [hy, h1 y hdiv, map_zero]
  · choose c hc using hf
    choose y hy using fun i => h2 (fun n => c n i)
    obtain ⟨x, hx⟩ := hs (fun i => t ^ k * y i)
    refine ⟨x, fun m i => ?_⟩
    obtain ⟨d, hd⟩ := hy i m
    refine ⟨d, ?_⟩
    rw [map_sub, map_sum, hx i, Finset.sum_congr rfl (fun n _ => hc n i), ← map_sum j, ← map_sub j]
    congr 1
    have e : t ^ k * y i - ∑ n ∈ Finset.range m, t ^ (n + k) * c n i =
        t ^ k * (y i - ∑ n ∈ Finset.range m, t ^ n * c n i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hd]
    ring

def crdZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    RW LL →+ Cb l :=
  (WittVector.constantCoeff : WCb l →+* Cb l).toAddMonoidHom.comp
    (crd (W := WCb l) (basisO LL) i).toAddMonoidHom

theorem crdZero_apply {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i) (x : RW LL) :
    crdZero LL i x = (crd (basisO LL) i x).coeff 0 := rfl

private theorem crd_tmul_lemma {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (o : ↥(OL LL)) (w : WCb l) :
    crd (W := WCb l) (basisO LL) i (o ⊗ₜ[ℤ_[l]] w) = (basisO LL).coord i o • w := by
  unfold crd
  rfl

set_option maxHeartbeats 1000000 in
private theorem crd_mul_lemma_2 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (q : WCb l) (y : RW LL) :
    crd (W := WCb l) (basisO LL) i (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] q) * y) =
      q * crd (W := WCb l) (basisO LL) i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma, mul_smul_comm]
  | add y z hy hz =>
    rw [mul_add, LinearMap.map_add, LinearMap.map_add, hy, hz]
    exact (mul_add q _ _).symm

private theorem expand_lemma_3 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (y : RW LL) :
    ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] crd (W := WCb l) (basisO LL) k y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [crd_tmul_lemma, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    simp_rw [Module.Basis.coord_apply]
    rw [Module.Basis.sum_repr]
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WCb l) :
    crd (W := WCb l) (basisO LL) i (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] w k) = w i := by
  simp [map_sum, crd_tmul_lemma, Finsupp.single_apply]

private theorem wdiv_lemma_5 {l : ℕ} [Fact l.Prime] (w : WCb l) (hw : w.coeff 0 = 0) :
    ∃ v : WCb l, w = (l : WCb l) * v := by
  have e : w = WittVector.verschiebung^[1] (w.shift 1) :=
    WittVector.eq_iterate_verschiebung (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hw)
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective (p := l) (R := Cb l)).2 (w.shift 1)
  refine ⟨z, ?_⟩
  rw [e, Function.iterate_one, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private theorem rwdiv_lemma_6 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (z : RW LL)
    (hz : ∀ i, (crd (W := WCb l) (basisO LL) i z).coeff 0 = 0) : ∃ r : RW LL, z = (l : RW LL) * r := by
  choose v hv using fun i => wdiv_lemma_5 _ (hz i)
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] v k, ?_⟩
  rw [← expand_lemma_3 LL z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hv k, ← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

private theorem cc_inclW_lemma_7 {l : ℕ} [Fact l.Prime] (w : Ainf l) :
    (inclW l w).coeff 0 = algebraMap (OCb l) (Cb l) (w.coeff 0) := by
  unfold inclW
  exact WittVector.map_coeff _ _ 0

private theorem cc_pi_lemma_8 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ) :
    (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 =
      algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [cc_inclW_lemma_7]
  congr 1
  change WittVector.constantCoeff (WittVector.teichmuller l (AI.εroot s) - 1) = _
  rw [map_sub, map_one]
  rfl

private theorem inclR_piR_lemma_9 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    piR AI LL s =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (AI.εroot s) - 1) := rfl

private theorem inclR_tmul_lemma_10 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (o : ↥(OL LL)) (w : Ainf l) :
    (inclR LL) (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] inclW l w := rfl

private theorem cc_inclR_lemma_11 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l) :
    ∃ c : OCb l, (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 = algebraMap (OCb l) (Cb l) c := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o w =>
    refine ⟨((basisO LL).coord i o • w).coeff 0, ?_⟩
    rw [inclR_tmul_lemma_10, crd_tmul_lemma, ← cc_inclW_lemma_7]
    congr 1
    exact (map_smul (inclWA l) _ _).symm
  | add a b ha hb =>
    obtain ⟨c1, h1⟩ := ha
    obtain ⟨c2, h2⟩ := hb
    refine ⟨c1 + c2, ?_⟩
    have e : (inclR LL) (a + b) = (inclR LL) a + (inclR LL) b := (inclR LL).toRingHom.map_add a b
    rw [e, LinearMap.map_add, (algebraMap (OCb l) (Cb l)).map_add, ← h1, ← h2]
    exact WittVector.add_coeff_zero _ _

private theorem coord_of_near_lemma_12 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL) (h : NearPi AI LL s n y)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c) := by
  unfold NearPi Near at h
  obtain ⟨a, r, rfl⟩ := h
  obtain ⟨c, hc⟩ := cc_inclR_lemma_11 LL i a
  refine ⟨c, ?_⟩
  rw [map_add, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, crdZero_apply, inclR_piR_lemma_9,
    Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2]
  change WittVector.constantCoeff (p := l) (R := Cb l) (_ * _) + _ = _
  rw [map_mul, map_pow]
  change (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
    (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 + _ = _
  rw [cc_pi_lemma_8, hc, map_mul, map_pow]
  simp

set_option maxHeartbeats 2000000 in
private theorem near_of_coord_lemma_13 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL)
    (h : ∀ i, ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c)) :
    NearPi AI LL s n y := by
  choose c hc using h
  let a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l := ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)
  obtain ⟨r, hr⟩ := rwdiv_lemma_6 LL (y - piR AI LL s ^ n * (inclR LL) a) (fun i => by
    have ha : (inclR LL) a = ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (c k)) := by
      change (inclR LL : RA LL →+* RW LL) (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [LinearMap.map_sub, inclR_piR_lemma_9, Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2, ha,
      crd_sum_lemma_4]
    change WittVector.constantCoeff (p := l) (R := Cb l) (_ - _) = 0
    rw [map_sub, map_mul, map_pow]
    change (crd (W := WCb l) (basisO LL) i y).coeff 0 -
      (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
        (inclW l (WittVector.teichmuller l (c i))).coeff 0 = 0
    rw [← crdZero_apply, hc, cc_pi_lemma_8, cc_inclW_lemma_7, WittVector.teichmuller_coeff_zero, map_mul,
      map_pow, sub_self])
  unfold NearPi Near
  exact ⟨a, r, sub_eq_iff_eq_add'.mp hr⟩

private theorem surj_lemma_14 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (c : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l) :
    ∃ x : RW LL, ∀ i, crdZero LL i x = algebraMap (OCb l) (Cb l) (c i) := by
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (c k)),
    fun i => ?_⟩
  rw [crdZero_apply, crd_sum_lemma_4, WittVector.teichmuller_coeff_zero]

theorem nearPi_sep_complete (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧
    ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) →
      ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  have key := sep_complete_of_coord (fun i => crdZero LL i) (algebraMap (OCb l) (Cb l))
    (IsFractionRing.injective (OCb l) (Cb l)) (AI.εroot s - 1) (surj_lemma_14 LL)
    (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).1 (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).2
  refine ⟨fun x hx => ?_, fun k f hf => ?_⟩
  · refine rwdiv_lemma_6 LL x fun i => ?_
    rw [← crdZero_apply]
    exact key.1 x (fun m i => coord_of_near_lemma_12 P AI LL s m x (hx m) i) i
  · obtain ⟨x, hx⟩ := key.2 k f (fun n i => coord_of_near_lemma_12 P AI LL s (n + k) (f n) (hf n) i)
    exact ⟨x, fun m => near_of_coord_lemma_13 P AI LL s (m + k) _ (hx m)⟩

end GlobalTheory.Decompl
