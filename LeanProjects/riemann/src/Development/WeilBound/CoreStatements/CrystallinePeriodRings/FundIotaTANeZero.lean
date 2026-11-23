import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
import GroundTheory.PAdicHodge.FundamentalSeqFixed

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem fund_eigen {A B : Type} [CommRing A] [CommRing B] {f : A →+* B}
    (hi : Function.Injective f) {F : B →+* B} {g : A →+* A} (hF : ∀ x, F (f x) = f (g x))
    {a t y : A} (ha : g a = a) (ht : g t = a * t) {b : B} (hb : F b = b) {m n : ℕ}
    (h : f a ^ m * f t ^ n * b = f y) : g y = a ^ n * y := by
  apply hi
  have h1 := congrArg F h
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, ha, ht, hb, map_mul] at h1
  rw [← h1, map_mul, map_pow, ← h]
  ring

theorem fund_read {A B R E : Type} [CommRing A] [CommRing B] [CommRing R] [Field E]
    {f : A →+* B} {ι : B →+* E} {c : A →+* E} (hc : Fac ι f c) {i : A →+* R} {j : R →+* E}
    (hj : Function.Injective j) (e : ∀ x, c x = j (i x)) {a t y : A} {b : B} {z : R}
    (hz : ι b = j z) {m n : ℕ} (h : f a ^ m * f t ^ n * b = f y) :
    i y = i a ^ m * i t ^ n * z := by
  apply hj
  have h1 := congrArg ι h
  rw [map_mul, map_mul, map_pow, map_pow, hc, hc, hc, e, e, e, hz] at h1
  rw [← h1, map_mul, map_mul, map_pow, map_pow]

theorem fund_map_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C} {G : C →+* C}
    {g : A →+* A} (hG : ∀ x, G (k x) = k (g x)) {p n : ℕ} {y : A} (h : g y = (p : A) ^ n * y) :
    G (k y) = (p : C) ^ n * k y := by
  rw [hG, h, map_mul, map_pow, map_natCast]

theorem fund_mem_span {R : Type} [CommRing R] {w u T T' z : R} {m n : ℕ} (hT : T' = T)
    (h : w = u ^ m * T' ^ n * z) : w ∈ Ideal.span {T ^ n} :=
  Ideal.mem_span_singleton'.2 ⟨u ^ m * z, by rw [h, hT]; ring⟩

theorem fund_cancel {A C R Q : Type} [CommRing A] [CommRing C] [CommRing R] [IsDomain R] [Field Q]
    {k : A →+* C} {i : A →+* R} {I : C →+* R} (hI : ∀ x, I (k x) = i x) {r : Q →+* C}
    {s : Q →+* R} (hr : ∀ q, I (r q) = s q) {p m n : ℕ} (hp : (p : Q) ≠ 0) {t y : A}
    (ht : i t ≠ 0) {z : R} (h : i y = i (p : A) ^ m * i t ^ n * z) {q : Q}
    (hq : k y = r q * k t ^ n) : z = s (q / (p : Q) ^ m) := by
  have h1 := congrArg I hq
  rw [map_mul, map_pow, hI, hI, hr, h, map_natCast, mul_right_comm] at h1
  have h2 := mul_right_cancel₀ (pow_ne_zero n ht) h1
  have h3 : s (((p : Q) ^ m)⁻¹) * (p : R) ^ m = 1 := by
    rw [← map_natCast s, ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero m hp), map_one]
  rw [div_eq_inv_mul, map_mul, ← h2, ← mul_assoc, h3, one_mul]

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem fund_iota_tA : ACris.iota ℂ_[l] l (Per6.tA l) = fontaineT (epsilon l) untilt_epsilon :=
  ACris.iota_periodT (untilt_epsilon (p := l))

theorem fund_iota_tA_ne_zero : ACris.iota ℂ_[l] l (Per6.tA l) ≠ 0 :=
  fund_iota_tA (l := l) ▸ fontaineT_ne_zero untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem fund_core {y : ACris.ACris ℂ_[l] l} {m n : ℕ} {z : Per6.BdRp l}
    (hy : ACris.phi ℂ_[l] l y = (l : ACris.ACris ℂ_[l] l) ^ n * y)
    (hz : ACris.iota ℂ_[l] l y = ACris.iota ℂ_[l] l (l : ACris.ACris ℂ_[l] l) ^ m *
      ACris.iota ℂ_[l] l (Per6.tA l) ^ n * z) :
    ∃ q : ℚ_[l], z = algebraMap ℚ_[l] (Per6.BdRp l) q := by
  obtain ⟨q, hq⟩ := ACris.exists_eq_algebraMap_mul_pow_of_phiPlus_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one n
    (fund_map_eigen ACris.phiPlus_algebraMap hy)
    (fund_mem_span fund_iota_tA ((ACris.iotaPlus_algebraMap y).trans hz))
  exact ⟨_, fund_cancel ACris.iotaPlus_algebraMap ACris.iotaPlus_algebraMap_padic
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) fund_iota_tA_ne_zero hz hq⟩

theorem fund_ιCD_qB (q : ℚ_[l]) : ιCD l (qB l q) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (algebraMap ℚ_[l] (Per6.BdRp l) q) := by
  refine (ιCD_qB q).trans ?_
  rw [frob_oD_apply, AlgHom.commutes]

theorem fund (b : Per6.Bcris l) (hφ : Per6.φB l b = b) (hb : ιCD l b ∈ Per6.FilD l 0) :
    ∃ q : ℚ_[l], qB l q = b := by
  obtain ⟨m, n, y, h⟩ := bcris_surj b
  obtain ⟨z, hz⟩ := (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).1 hb
  obtain ⟨q, hq⟩ := fund_core
    (fund_eigen frob_cB_injective φB_cB (map_natCast _ l) frob_phi_tA hφ h)
    (fund_read (ιCD_fac l)
      (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)) cD_apply hz h)
  exact ⟨q, ιCD_injective ((fund_ιCD_qB q).trans
    ((congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) hq).symm.trans hz.symm))⟩

end PositivityTheory.LocInh
