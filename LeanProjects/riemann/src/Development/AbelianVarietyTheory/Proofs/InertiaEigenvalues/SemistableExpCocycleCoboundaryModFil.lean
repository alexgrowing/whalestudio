import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.Cob

theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [CharP R l] [PerfectRing R l]
    (f g : ℤ_[l] →+* WittVector l R) (x : ℤ_[l]) : f x = g x := by
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : WittVector l R)}) (WittVector l R)) _ fun n => ?_)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[l]) + y * (l : ℤ_[l]) ^ n := by rw [hy]; ring
  have h : f x - g x = (f y - g y) * (l : WittVector l R) ^ n := by
    have hf := congrArg f hx
    have hg := congrArg g hx
    simp only [map_add, map_mul, map_pow, map_natCast] at hf hg
    rw [hf, hg]
    ring
  rw [SModEq.zero, h, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def texp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (x : S) :
    Matrix (Fin d) (Fin d) S :=
  ∑ n ∈ Finset.range d, (ψ ((n.factorial : ℚ)⁻¹) * x ^ n) • N ^ n

theorem texp_eq_exp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (x : S) :
    letI : Algebra ℚ S := ψ.toAlgebra
    texp ψ N x = IsNilpotent.exp (x • N) := by
  letI : Algebra ℚ S := ψ.toAlgebra
  have h : (x • N) ^ d = 0 := by rw [smul_pow, hN, smul_zero]
  rw [IsNilpotent.exp_eq_sum h, texp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_pow, ← algebraMap_smul S ((n.factorial : ℚ)⁻¹), smul_smul]
  rfl

theorem texp_mul {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (x y : S) : texp ψ N x * texp ψ N y = texp ψ N (x + y) := by
  letI : Algebra ℚ S := ψ.toAlgebra
  have hn : ∀ w : S, IsNilpotent (w • N) := fun w => ⟨d, by rw [smul_pow, hN, smul_zero]⟩
  rw [texp_eq_exp ψ N hN, texp_eq_exp ψ N hN, texp_eq_exp ψ N hN, add_smul,
    IsNilpotent.exp_add_of_commute (((Commute.refl N).smul_left x).smul_right y) (hn x) (hn y)]

theorem sum_eq_smul_texp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (A x : S) :
    ∑ n ∈ Finset.range d, (A * ψ ((n.factorial : ℚ)⁻¹) * x ^ n) • N ^ n = A • texp ψ N x := by
  rw [texp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_smul, mul_assoc]

theorem texp_cocycle {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (A B q p v z Y : S) (hpv : p * v = q) :
    (∑ n ∈ Finset.range d, (A * ψ ((n.factorial : ℚ)⁻¹) * (q * z) ^ n) • N ^ n) *
      (∑ n ∈ Finset.range d, (B * ψ ((n.factorial : ℚ)⁻¹) * (-p * (Y + v * z)) ^ n) • N ^ n) =
    A • ∑ n ∈ Finset.range d, (B * ψ ((n.factorial : ℚ)⁻¹) * (-p * Y) ^ n) • N ^ n := by
  rw [sum_eq_smul_texp, sum_eq_smul_texp, sum_eq_smul_texp, Matrix.smul_mul, Matrix.mul_smul,
    texp_mul ψ N hN, smul_smul, smul_smul, mul_comm A B]
  congr 2
  linear_combination (-z) * hpv

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob

theorem map_sum_smul_pow {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (a : ℕ → R) (x : R) (M : Matrix (Fin d) (Fin d) R) :
    (∑ n ∈ Finset.range d, (a n * x ^ n) • M ^ n).map h =
      ∑ n ∈ Finset.range d, (h (a n) * h x ^ n) • (M.map h) ^ n := by
  rw [← RingHom.mapMatrix_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : h.mapMatrix ((a n * x ^ n) • M ^ n) = h (a n * x ^ n) • h.mapMatrix (M ^ n) := by
    ext i j; simp
  rw [e, map_pow, map_mul, map_pow, RingHom.mapMatrix_apply]

theorem map_smul_matrix {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map h = h c • M.map h := by
  ext i j; simp

variable {l : ℕ} [Fact l.Prime]

def qD (C : Core l) : ℚ →+* Per.BdRp l :=
  (C.o.comp (algebraMap ℚ_[l] (Om l))).comp (algebraMap ℚ ℚ_[l])

theorem aDp_zA_ecoef (C : Core l) {k₀ k n : ℕ} (h : ‖ecoefQ l k₀ k n‖ ≤ 1) :
    aDp l (Per.zA l (ecoef l k₀ k n)) =
      (l : Per.BdRp l) ^ k₀ * qD C ((n.factorial : ℚ)⁻¹) * (qD C ((l : ℚ)⁻¹) ^ k) ^ n := by
  rw [← C.o_sec.z, ecoef_val h]
  have e : ecoefQ l k₀ k n =
      algebraMap ℚ ℚ_[l] ((l : ℚ) ^ k₀ * (n.factorial : ℚ)⁻¹ * (((l : ℚ)⁻¹) ^ k) ^ n) := by
    simp only [ecoefQ, map_mul, map_pow, map_inv₀, map_natCast]
    ring
  rw [e]
  simp only [qD, RingHom.comp_apply, map_mul, map_pow, map_natCast]

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob
variable {l : ℕ} [Fact l.Prime]

theorem coef_Λ (C : Core l) {K : FinExt l} (bk : BK K) {I : Ideal (Per.BdRp l)} (H : bk.S →+* Per.BdRp l ⧸ I)
    (hH : ∀ w, H (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w))) {KK L n : ℕ}
    (hn : ‖ecoefQ l KK L n‖ ≤ 1) :
    H (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) ((-1) ^ n * ecoef l KK L n))) =
      (l : Per.BdRp l ⧸ I) ^ KK * Ideal.Quotient.mk I (qD C ((n.factorial : ℚ)⁻¹)) *
        (-(Ideal.Quotient.mk I (qD C ((l : ℚ)⁻¹)) ^ L)) ^ n := by
  rw [hH, AlgHom.commutes, padicInt_hom_ext_pt (algebraMap ℤ_[l] (Ainf l)) (Per.zA l)]
  rw [map_mul, map_pow, map_neg, map_one, map_mul, map_pow, map_neg, map_one, aDp_zA_ecoef C hn]
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob

theorem cocycle_cob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → Mn ^ d = 0 → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∀ m : ℕ, ∃ (kk : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ kk • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((GlobalTheory.SstPer.kap C bk k₀ k Mn (c g) * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C _ d k k₀ Mn c hk hMn hlog m
  obtain ⟨k', s, hEs, hs⟩ := hlog m
  obtain ⟨e, m', hm', hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l
    (Fact.out : l.Prime).ne_one
  have hnorm : ∀ n < d, ‖ecoefQ l (e + (k' + k) * d) (k' + k) n‖ ≤ 1 :=
    fun n hn => ecoefQ_norm_le (k' + k) hm' hd hn
  let cf : ℕ → bk.S := fun n =>
    PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) ((-1) ^ n * ecoef l (e + (k' + k) * d) (k' + k) n))
  let Λ : Matrix (Fin d) (Fin d) bk.S :=
    ∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n
  refine ⟨e + (k' + k) * d, Λ, ?_, ?_⟩
  · intro i j
    rcases d with _ | d
    · exact i.elim0
    have h0 : ecoef l (e + (k' + k) * (d + 1)) (k' + k) 0 = (l : ℤ_[l]) ^ (e + (k' + k) * (d + 1)) := by
      apply Subtype.ext
      rw [ecoef_val (hnorm 0 d.succ_pos)]
      simp [ecoefQ]
    have hc0 : cf 0 = (l : bk.S) ^ (e + (k' + k) * (d + 1)) := by
      simp only [cf, pow_zero, one_mul, h0, map_pow, map_natCast]
    have hΛ : Λ - (l : bk.S) ^ (e + (k' + k) * (d + 1)) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) bk.S) =
        ∑ n ∈ Finset.range d, (cf (n + 1) * s ^ (n + 1)) • (Mn.map PowerSeries.C) ^ (n + 1) := by
      simp only [Λ]
      rw [Finset.sum_range_succ', hc0, pow_zero, pow_zero, mul_one, add_sub_cancel_right]
    rw [hΛ, Matrix.sum_apply]
    refine Finset.dvd_sum fun n _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hEs.trans (dvd_pow_self s n.succ_ne_zero)) _) _
  · intro g i j
    let I := Per.FilP l m
    let Θ : Per.Acris l →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp C.j
    let ψ : ℚ →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp (qD C)
    let lam : Per.BdRp l ⧸ I := ψ ((l : ℚ)⁻¹)
    let φ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev
    let H0 : bk.S →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp ((aDp l).comp bk.ev)
    let H1 : bk.S →+* Per.BdRp l ⧸ I :=
      (Ideal.Quotient.mk I).comp ((aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev))
    let N : Matrix (Fin d) (Fin d) (Per.BdRp l ⧸ I) := (Mn.map PowerSeries.C).map H0
    let z : Per.BdRp l ⧸ I := Ideal.Quotient.mk I (aDp l (Per.zA l (c g)) * C.j C.t)
    let Y : Per.BdRp l ⧸ I := Ideal.Quotient.mk I (aDp l (bk.ev s))
    have hj : ∀ x : Ainf l, C.j (algebraMap (Ainf l) (Per.Acris l) x) = aDp l x :=
      fun x => by
        have h := C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
        rw [← GlobalTheory.RingIface.tower, Subalgebra.coe_algebraMap] at h
        exact h
    have hσ : ∀ x : Ainf l, sigA (g : GQ l) (algebraMap (Ainf l) (Per.Acris l) x) =
        algebraMap (Ainf l) (Per.Acris l) (Per.σA (g : GQ l) x) :=
      fun x => (GlobalTheory.CrisMaps.sigA_extends (g : GQ l)).alg x
    have hC0 : ∀ w, H0 (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w)) := fun w => by
      simp only [H0, RingHom.comp_apply, bk.ev_C]
    have hC1 : ∀ w, H1 (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w)) := fun w => by
      simp only [H1, RingHom.comp_apply, bk.ev_C, bk.gal_w]
    have m0 : (Λ.map φ).map Θ = Λ.map H0 := by
      ext a b
      simp only [Matrix.map_apply, Θ, φ, H0, RingHom.comp_apply, hj]
    have m1 : ((Λ.map φ).map (sigA (g : GQ l))).map Θ = Λ.map H1 := by
      ext a b
      simp only [Matrix.map_apply, Θ, φ, H1, RingHom.comp_apply, hσ, hj]
    have hN : N ^ d = 0 := by
      simp only [N, ← RingHom.mapMatrix_apply, ← map_pow, hMn, map_zero]
    have hN1 : (Mn.map PowerSeries.C).map H1 = N := by
      ext a b
      simp only [N, Matrix.map_apply, hC0, hC1]
    have hNk : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map Θ = N := by
      ext a b
      simp only [N, Matrix.map_apply, hC0, Θ, RingHom.comp_apply, hj, bk.ev_C]
    have hY : H1 s = Y + (l : Per.BdRp l ⧸ I) ^ k' * z := by
      have h := (Ideal.Quotient.eq_zero_iff_mem (I := I)).2 (hs g)
      simp only [map_sub, map_mul, map_pow, map_natCast] at h
      simp only [H1, Y, z, RingHom.comp_apply, map_mul]
      linear_combination h
    have e0 : (Λ.map φ).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ (e + (k' + k) * d) * ψ ((n.factorial : ℚ)⁻¹) *
          (-(lam ^ (k' + k)) * Y) ^ n) • N ^ n := by
      rw [m0]
      show (∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n).map H0 = _
      rw [map_sum_smul_pow H0 cf s]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [show H0 (cf n) = _ from coef_Λ C bk H0 hC0 (hnorm n (Finset.mem_range.1 hn))]
      simp only [ψ, lam, RingHom.comp_apply]
      congr 1
      simp only [H0, Y, RingHom.comp_apply]
      ring
    have e1 : ((Λ.map φ).map (sigA (g : GQ l))).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ (e + (k' + k) * d) * ψ ((n.factorial : ℚ)⁻¹) *
          (-(lam ^ (k' + k)) * (Y + (l : Per.BdRp l ⧸ I) ^ k' * z)) ^ n) • N ^ n := by
      rw [m1]
      show (∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n).map H1 = _
      rw [map_sum_smul_pow H1 cf s, hN1, hY]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [show H1 (cf n) = _ from coef_Λ C bk H1 hC1 (hnorm n (Finset.mem_range.1 hn))]
      simp only [ψ, lam, RingHom.comp_apply]
      congr 1
      rw [mul_pow (-_) (Y + _)]
      ring
    have eK : (kap C bk k₀ k Mn (c g)).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ k₀ * ψ ((n.factorial : ℚ)⁻¹) * (lam ^ k * z) ^ n) • N ^ n := by
      unfold kap
      rw [map_sum_smul_pow Θ (fun n => algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k n))), hNk]
      refine Finset.sum_congr rfl fun n hn => ?_
      have h1 : Θ (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k n))) =
          (l : Per.BdRp l ⧸ I) ^ k₀ * ψ ((n.factorial : ℚ)⁻¹) * (lam ^ k) ^ n := by
        simp only [Θ, RingHom.comp_apply, hj]
        rw [aDp_zA_ecoef C (hk n (Finset.mem_range.1 hn))]
        simp only [ψ, lam, map_mul, map_pow, map_natCast, RingHom.comp_apply]
      have h2 : Θ (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (c g)) * C.t) = z := by
        simp only [Θ, z, RingHom.comp_apply, map_mul, hj]
      rw [h1, h2]
      congr 1
      ring
    have hpv : lam ^ (k' + k) * (l : Per.BdRp l ⧸ I) ^ k' = lam ^ k := by
      have hl : lam * (l : Per.BdRp l ⧸ I) = 1 := by
        have h := congrArg ψ (inv_mul_cancel₀ (by exact_mod_cast (Fact.out : l.Prime).ne_zero : (l : ℚ) ≠ 0))
        rw [map_mul, map_natCast, map_one] at h
        exact h
      rw [pow_add, mul_comm (lam ^ k'), mul_assoc, ← mul_pow, hl, one_pow, mul_one]
    have hz : (kap C bk k₀ k Mn (c g) * (Λ.map φ).map (sigA (g : GQ l)) -
        (l : Per.Acris l) ^ k₀ • Λ.map φ).map Θ = 0 := by
      rw [← RingHom.mapMatrix_apply, map_sub, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, map_smul_matrix, eK, e1, e0,
        texp_cocycle ψ N hN _ _ _ _ _ z Y hpv, map_pow, map_natCast, sub_self]
    have hij := congrFun (congrFun hz i) j
    rw [Matrix.map_apply] at hij
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hij

end GlobalTheory.SstPer.Cob
