import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.OrthFrame

variable {g : ℕ}

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
lemma _root_.GlobalTheory.MomOne.OrthFrame.beta_add_left (d : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) (x y z : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d H (x + y) z = _root_.Formalism.L2.Ker.JMB.beta d H x z + _root_.Formalism.L2.Ker.JMB.beta d H y z := by
  simp only [_root_.Formalism.L2.Ker.JMB.beta, _root_.Formalism.L2.Ker.JMB.hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
lemma _root_.GlobalTheory.MomOne.OrthFrame.beta_smul_left (d : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x z : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d H (c • x) z = c * _root_.Formalism.L2.Ker.JMB.beta d H x z := by
  simp only [_root_.Formalism.L2.Ker.JMB.beta, _root_.Formalism.L2.Ker.JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

noncomputable def betaL (d : ℕ) (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun x := beta d H x z
  map_add' x y := beta_add_left d H x y z
  map_smul' c x := beta_smul_left d H c x z

lemma rankOne_base_weight_eq_cmTheta (d : ℕ) : w0 d = wK d := rfl

end GlobalTheory.MomOne.OrthFrame

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma w0_eq_wK (d : ℕ) : _root_.Formalism.L2.Ker.JMB.w0 d = _root_.GlobalTheory.MomOne.wK d := by
  unfold _root_.Formalism.L2.Ker.JMB.w0 _root_.Formalism.L2.Ker.JMB.rtd _root_.GlobalTheory.MomOne.wK; rfl

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma mem_OK_iff' (d : ℕ) (b : ℂ) :
    b ∈ _root_.Formalism.L2.Ker.JMB.OK d ↔ ∃ u v : ℤ, b = u + v * _root_.GlobalTheory.MomOne.wK d := by
  unfold _root_.Formalism.L2.Ker.JMB.OK; rw [w0_eq_wK]; rfl

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma smul_mem_of_mem_OK {d : ℕ} {L : Submodule ℤ (Fin g → ℂ)}
    (hL : ∀ x ∈ L, _root_.Formalism.L2.Ker.JMB.w0 d • x ∈ L) {c : ℂ} (hc : c ∈ _root_.Formalism.L2.Ker.JMB.OK d) {x : Fin g → ℂ}
    (hx : x ∈ L) : c • x ∈ L := by
  rw [mem_OK_iff'] at hc
  obtain ⟨u, v, rfl⟩ := hc
  rw [add_smul, mul_smul, ← w0_eq_wK, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact L.add_mem (L.smul_mem u hx) (L.smul_mem v (hL x hx))

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma natCast_mul_mem_OK {d : ℕ} {b : ℂ} (hb : b ∈ _root_.Formalism.L2.Ker.JMB.OK d) (n : ℕ) :
    (n : ℂ) * b ∈ _root_.Formalism.L2.Ker.JMB.OK d := by
  rw [mem_OK_iff'] at hb ⊢
  obtain ⟨u, v, rfl⟩ := hb
  exact ⟨n * u, n * v, by push_cast; ring⟩

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma conj_beta_eq_beta_swap (d : ℕ) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (x z : Fin g → ℂ) : conj (_root_.Formalism.L2.Ker.JMB.beta d H x z) = _root_.Formalism.L2.Ker.JMB.beta d H z x := by
  simp only [_root_.Formalism.L2.Ker.JMB.beta, _root_.Formalism.L2.Ker.JMB.hf, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (starRingEnd ℂ) (H j i) = H i j from hH.apply i j]
  ring

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma beta_sub_right (d : ℕ) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (x y z : Fin g → ℂ) : _root_.Formalism.L2.Ker.JMB.beta d H x (y - z) = _root_.Formalism.L2.Ker.JMB.beta d H x y - _root_.Formalism.L2.Ker.JMB.beta d H x z := by
  rw [← conj_beta_eq_beta_swap d hH (y - z) x, ← conj_beta_eq_beta_swap d hH y x,
    ← conj_beta_eq_beta_swap d hH z x, ← map_sub]
  congr 1
  exact (_root_.GlobalTheory.MomOne.OrthFrame.betaL d H x).map_sub y z

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma beta_smul_right' (d : ℕ) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (c : ℂ) (x z : Fin g → ℂ) : _root_.Formalism.L2.Ker.JMB.beta d H x (c • z) = conj c * _root_.Formalism.L2.Ker.JMB.beta d H x z := by
  rw [← conj_beta_eq_beta_swap d hH, _root_.GlobalTheory.MomOne.OrthFrame.beta_smul_left, map_mul, conj_beta_eq_beta_swap d hH]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma beta_sum_right' (d : ℕ) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    {ι : Type*} (s : Finset ι) (f : ι → Fin g → ℂ) (x : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d H x (∑ i ∈ s, f i) = ∑ i ∈ s, _root_.Formalism.L2.Ker.JMB.beta d H x (f i) := by
  rw [← conj_beta_eq_beta_swap d hH]
  have := map_sum (_root_.GlobalTheory.MomOne.OrthFrame.betaL d H x) f s
  simp only [_root_.GlobalTheory.MomOne.OrthFrame.betaL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun i _ => conj_beta_eq_beta_swap d hH _ _

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma im_int_add_mul_wK (d : ℕ) (u v : ℤ) :
    ((u : ℂ) + v * _root_.GlobalTheory.MomOne.wK d).im = v * (√(d : ℝ) / 2) := by
  simp [Complex.add_im, Complex.mul_im, _root_.GlobalTheory.MomOne.OKArith.im_w]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma im_hf_eq_of_beta_eq {d : ℕ} (hd : 0 < d) {H : Matrix (Fin g) (Fin g) ℂ}
    {x z : Fin g → ℂ} {u v : ℤ}
    (huv : _root_.Formalism.L2.Ker.JMB.beta d H x z = u + v * _root_.GlobalTheory.MomOne.wK d) :
    (_root_.Formalism.L2.Ker.JMB.hf H x z).im = v := by
  have h := congrArg Complex.im huv
  rw [im_int_add_mul_wK] at h
  simp only [_root_.Formalism.L2.Ker.JMB.beta, Complex.im_ofReal_mul] at h
  have h0 : √(d : ℝ) / 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ h0 (h.trans (mul_comm _ _))

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma exists_pos_nat_beta_self_eq {d : ℕ} (hd : 0 < d) {H : Matrix (Fin g) (Fin g) ℂ}
    (hH : H.PosDef) {w : Fin g → ℂ} (hw : w ≠ 0) (hb : _root_.Formalism.L2.Ker.JMB.beta d H w w ∈ _root_.Formalism.L2.Ker.JMB.OK d) :
    ∃ n : ℕ, 0 < n ∧ _root_.Formalism.L2.Ker.JMB.beta d H w w = n := by
  obtain ⟨u, v, huv⟩ := (mem_OK_iff' d _).1 hb
  have hpos : 0 < _root_.Formalism.L2.Ker.JMB.hf H w w := by
    have := hH.dotProduct_mulVec_pos (x := star w) (by simpa using hw)
    convert this using 1
    simp [_root_.Formalism.L2.Ker.JMB.hf, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Complex.star_def]
  rw [Complex.pos_iff] at hpos
  have hv : v = 0 := by
    have := im_hf_eq_of_beta_eq hd huv
    rw [← hpos.2] at this
    exact_mod_cast this.symm
  subst hv
  have hre : _root_.Formalism.L2.Ker.JMB.beta d H w w = u := by simpa using huv
  have hu : (0 : ℝ) < u := by
    have := congrArg Complex.re hre
    simp only [_root_.Formalism.L2.Ker.JMB.beta, Complex.re_ofReal_mul, Complex.intCast_re] at this
    rw [← this]
    exact mul_pos (by positivity) hpos.1
  have hu' : 0 < u := by exact_mod_cast hu
  refine ⟨u.toNat, by omega, ?_⟩
  rw [hre]
  exact_mod_cast (Int.toNat_of_nonneg hu'.le).symm

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma beta_add_right' (d : ℕ) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (x y z : Fin g → ℂ) : _root_.Formalism.L2.Ker.JMB.beta d H x (y + z) = _root_.Formalism.L2.Ker.JMB.beta d H x y + _root_.Formalism.L2.Ker.JMB.beta d H x z := by
  rw [← conj_beta_eq_beta_swap d hH, _root_.GlobalTheory.MomOne.OrthFrame.beta_add_left, map_add, conj_beta_eq_beta_swap d hH,
    conj_beta_eq_beta_swap d hH]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma div_mem_of_norms_dvd_lemma_9 {d k q : ℕ} (hd : 0 < d) (hk : 4 * k = d + 1) (hq : q.Prime)
    (hqd : ¬ q ∣ d) {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian) {w₁ w₂ : Fin g → ℂ}
    (hb : _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂ ∈ _root_.Formalism.L2.Ker.JMB.OK d)
    (h₁ : ∃ n : ℤ, _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₁ = q * n) (h₂ : ∃ n : ℤ, _root_.Formalism.L2.Ker.JMB.beta d H w₂ w₂ = q * n)
    (h₃ : ∃ n : ℤ, _root_.Formalism.L2.Ker.JMB.beta d H (w₁ + w₂) (w₁ + w₂) = q * n)
    (h₄ : ∃ n : ℤ, _root_.Formalism.L2.Ker.JMB.beta d H (w₁ + _root_.Formalism.L2.Ker.JMB.w0 d • w₂) (w₁ + _root_.Formalism.L2.Ker.JMB.w0 d • w₂) = q * n) :
    _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂ / q ∈ _root_.Formalism.L2.Ker.JMB.OK d := by
  obtain ⟨u, v, huv⟩ := (mem_OK_iff' d _).1 hb
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  obtain ⟨n₃, e₃⟩ := h₃
  obtain ⟨n₄, e₄⟩ := h₄
  rw [w0_eq_wK] at e₄
  have hsq := _root_.GlobalTheory.MomOne.OKArith.w_sq hk
  have hcω := _root_.GlobalTheory.MomOne.OKArith.conj_w d
  have hc : conj (_root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂) = u + v * (1 - _root_.GlobalTheory.MomOne.wK d) := by
    rw [huv, _root_.GlobalTheory.MomOne.OKArith.conj_el]
  have E₃ : _root_.Formalism.L2.Ker.JMB.beta d H (w₁ + w₂) (w₁ + w₂) = _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₁ + _root_.Formalism.L2.Ker.JMB.beta d H w₂ w₂
      + _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂ + conj (_root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂) := by
    rw [_root_.GlobalTheory.MomOne.OrthFrame.beta_add_left, beta_add_right' d hH, beta_add_right' d hH,
      ← conj_beta_eq_beta_swap d hH w₁ w₂]
    ring
  have E₄ : _root_.Formalism.L2.Ker.JMB.beta d H (w₁ + _root_.GlobalTheory.MomOne.wK d • w₂)
      (w₁ + _root_.GlobalTheory.MomOne.wK d • w₂) = _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₁
      + conj (_root_.GlobalTheory.MomOne.wK d) * _root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂
      + _root_.GlobalTheory.MomOne.wK d * conj (_root_.Formalism.L2.Ker.JMB.beta d H w₁ w₂)
      + _root_.GlobalTheory.MomOne.wK d * conj (_root_.GlobalTheory.MomOne.wK d)
        * _root_.Formalism.L2.Ker.JMB.beta d H w₂ w₂ := by
    rw [_root_.GlobalTheory.MomOne.OrthFrame.beta_add_left, beta_add_right' d hH, beta_add_right' d hH,
      _root_.GlobalTheory.MomOne.OrthFrame.beta_smul_left, _root_.GlobalTheory.MomOne.OrthFrame.beta_smul_left, beta_smul_right' d hH,
      beta_smul_right' d hH, ← conj_beta_eq_beta_swap d hH w₁ w₂]
    ring
  have I₃ : (q : ℤ) * n₃ = q * n₁ + q * n₂ + (2 * u + v) := by
    have : (q : ℂ) * n₃ = q * n₁ + q * n₂ + (2 * u + v) := by
      rw [← e₃, E₃, e₁, e₂, hc, huv]; ring
    exact_mod_cast this
  have I₄ : (q : ℤ) * n₄ = q * n₁ + k * (q * n₂) + (u + 2 * k * v) := by
    have : (q : ℂ) * n₄ = q * n₁ + k * (q * n₂) + (u + 2 * k * v) := by
      rw [← e₄, E₄, e₁, e₂, hc, hcω, huv]
      linear_combination (-(2 * (v : ℂ) + q * n₂)) * hsq
    exact_mod_cast this
  have hk' : (4 * k : ℤ) = d + 1 := by exact_mod_cast hk
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqd' : ¬ (q : ℤ) ∣ d := by exact_mod_cast hqd
  have hqu : (q : ℤ) ∣ d * u :=
    ⟨2 * k * (n₃ - n₁ - n₂) - (n₄ - n₁ - k * n₂), by
      linear_combination (-2 * (k : ℤ)) * I₃ + I₄ + (-u) * hk'⟩
  have hqv : (q : ℤ) ∣ d * v :=
    ⟨2 * (n₄ - n₁ - k * n₂) - (n₃ - n₁ - n₂), by
      linear_combination (-2 : ℤ) * I₄ + I₃ + (-v) * hk'⟩
  obtain ⟨u', rfl⟩ := (hqZ.dvd_or_dvd hqu).resolve_left hqd'
  obtain ⟨v', rfl⟩ := (hqZ.dvd_or_dvd hqv).resolve_left hqd'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [mem_OK_iff']
  refine ⟨u', v', ?_⟩
  rw [huv]
  push_cast
  field_simp

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma div_mem_OK_of_mul_div_mem_of_coprime {d q A : ℕ} (hd : 0 < d) (hq : q.Prime) {c : ℂ}
    (hc : c ∈ _root_.Formalism.L2.Ker.JMB.OK d) (h : (A : ℂ) * c / q ∈ _root_.Formalism.L2.Ker.JMB.OK d) (hA : Nat.Coprime A q) :
    c / q ∈ _root_.Formalism.L2.Ker.JMB.OK d := by
  obtain ⟨u, v, rfl⟩ := (mem_OK_iff' d _).1 hc
  obtain ⟨u', v', h'⟩ := (mem_OK_iff' d _).1 h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [div_eq_iff hq0] at h'
  have hcoord : (((A * u : ℤ) : ℂ) + ((A * v : ℤ) : ℂ) * _root_.GlobalTheory.MomOne.wK d)
      = ((q * u' : ℤ) : ℂ) + ((q * v' : ℤ) : ℂ) * _root_.GlobalTheory.MomOne.wK d := by
    push_cast; linear_combination h'
  obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.MomOne.OKArith.coord_unique hd hcoord
  have hcop : IsCoprime (q : ℤ) (A : ℤ) := Nat.isCoprime_iff_coprime.mpr hA.symm
  obtain ⟨u₁, rfl⟩ :=
    hcop.dvd_of_dvd_mul_left (show (q : ℤ) ∣ A * u from ⟨u', e₁⟩)
  obtain ⟨v₁, rfl⟩ :=
    hcop.dvd_of_dvd_mul_left (show (q : ℤ) ∣ A * v from ⟨v', e₂⟩)
  rw [mem_OK_iff']
  refine ⟨u₁, v₁, ?_⟩
  push_cast
  field_simp

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma conj_mem_OK {d : ℕ} {b : ℂ} (hb : b ∈ _root_.Formalism.L2.Ker.JMB.OK d) :
    conj b ∈ _root_.Formalism.L2.Ker.JMB.OK d := by
  rw [mem_OK_iff'] at hb ⊢
  obtain ⟨u, v, rfl⟩ := hb
  refine ⟨u + v, -v, ?_⟩
  rw [_root_.GlobalTheory.MomOne.OKArith.conj_el]
  push_cast; ring

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
private lemma exists_orthogonal_vector_norm_coprime {q : ℕ} (hq : q.Prime) (S : _root_.Formalism.L2.Ker.JMB.Setup g)
    (hS : S.Ok) (hqd : ¬ q ∣ S.d) {r : ℕ} (hr : r < g) (x : Fin r → Fin g → ℂ) (a : Fin r → ℕ)
    (hx : ∀ i, x i ∈ S.La)
    (horth : ∀ i j, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) :
    ∃ w ∈ S.La, (∀ i, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm w (x i) = 0) ∧
      ∃ n : ℕ, 0 < n ∧ Nat.Coprime n q ∧ _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm w w = n := by
  obtain ⟨hdp, hd16, hH, -, hspan, hω, hint, hdual⟩ := hS
  have hd : 0 < S.d := hdp.pos
  obtain ⟨k, hk⟩ : ∃ k, 4 * k = S.d + 1 := ⟨(S.d + 1) / 4, by omega⟩
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set A := ∏ i, a i with hAdef
  have hAq : Nat.Coprime A q := Nat.Coprime.prod_left fun i _ => (ha i).2
  have hdvd : ∀ i, a i ∣ A := fun i => Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have hA0 : (A : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.2 fun i _ => (ha i).1.ne')
  let P : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (A : ℂ) • LinearMap.id -
    ∑ i, ((A / a i : ℕ) : ℂ) • (_root_.GlobalTheory.MomOne.OrthFrame.betaL S.d S.Hm (x i)).smulRight (x i)
  have hP : ∀ y, P y = (A : ℂ) • y -
      ∑ i, (((A / a i : ℕ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm y (x i)) • x i := by
    intro y
    simp [P, _root_.GlobalTheory.MomOne.OrthFrame.betaL, mul_smul]
  have hPL : ∀ y ∈ S.La, P y ∈ S.La := by
    intro y hy
    rw [hP, Nat.cast_smul_eq_nsmul]
    exact S.La.sub_mem (S.La.nsmul_mem hy A) (S.La.sum_mem fun i _ =>
      smul_mem_of_mem_OK hω (natCast_mul_mem_OK (hint y hy (x i) (hx i)) _)
        (hx i))
  have hPorth : ∀ y j, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) (x j) = 0 := by
    intro y j
    have e : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) (x j) = _root_.GlobalTheory.MomOne.OrthFrame.betaL S.d S.Hm (x j) (P y) := rfl
    rw [e, hP, map_sub, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, _root_.GlobalTheory.MomOne.OrthFrame.betaL, LinearMap.coe_mk,
      AddHom.coe_mk, horth, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_assoc, mul_comm (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm y (x j)), ← mul_assoc, ← Nat.cast_mul,
      Nat.div_mul_cancel (hdvd j)]
    ring
  have hPP : ∀ y z, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) (P z) = (A : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) z := by
    intro y z
    rw [hP z, beta_sub_right S.d hH.1, beta_smul_right' S.d hH.1, beta_sum_right' S.d hH.1]
    simp [beta_smul_right' S.d hH.1, hPorth]
  have hPidem : ∀ y, P (P y) = (A : ℂ) • P y := by
    intro y
    rw [hP (P y)]
    simp [hPorth]
  by_contra hcon
  push_neg at hcon
  have hdivall : ∀ y ∈ S.La, ∃ m : ℤ, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) (P y) = q * m := by
    intro y hy
    by_cases h0 : P y = 0
    · exact ⟨0, by simp [h0, _root_.Formalism.L2.Ker.JMB.beta, _root_.Formalism.L2.Ker.JMB.hf]⟩
    obtain ⟨n, hn, hnw⟩ := exists_pos_nat_beta_self_eq hd hH h0 (hint _ (hPL y hy) _ (hPL y hy))
    have hnc : ¬ Nat.Coprime n q := fun hc => hcon _ (hPL y hy) (hPorth y) n hn hc hnw
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hq, not_not] at hnc
    obtain ⟨m, rfl⟩ := hnc
    exact ⟨m, by rw [hnw]; push_cast; ring⟩
  have hdiv : ∀ y ∈ S.La, ∀ z ∈ S.La, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (P y) z / q ∈ _root_.Formalism.L2.Ker.JMB.OK S.d := by
    intro y hy z hz
    have hpol := div_mem_of_norms_dvd_lemma_9 hd hk hq hqd hH.1 (hint _ (hPL y hy) _ (hPL z hz))
      (hdivall y hy) (hdivall z hz)
      (by rw [← map_add]; exact hdivall _ (S.La.add_mem hy hz))
      (by rw [← LinearMap.map_smul, ← map_add]; exact hdivall _ (S.La.add_mem hy (hω z hz)))
    rw [hPP] at hpol
    exact div_mem_OK_of_mul_div_mem_of_coprime hd hq (hint _ (hPL y hy) z hz) hpol hAq
  have hdivL : ∀ y ∈ S.La, (q : ℂ)⁻¹ • P y ∈ S.La := by
    intro y hy
    apply hdual
    intro z hz
    have hb : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm z ((q : ℂ)⁻¹ • P y) ∈ _root_.Formalism.L2.Ker.JMB.OK S.d := by
      rw [beta_smul_right' S.d hH.1, ← conj_beta_eq_beta_swap S.d hH.1 (P y) z, ← map_mul,
        inv_mul_eq_div]
      exact conj_mem_OK (hdiv y hy z hz)
    obtain ⟨u, v, huv⟩ := (mem_OK_iff' _ _).1 hb
    exact ⟨v, im_hf_eq_of_beta_eq hd huv⟩
  have hex : ∃ y ∈ S.La, P y ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : Submodule.span ℝ (S.La : Set (Fin g → ℂ)) ≤ LinearMap.ker (P.restrictScalars ℝ) :=
      Submodule.span_le.2 fun y hy => hall y hy
    rw [hspan, top_le_iff] at hle
    have htop : Submodule.span ℂ (Set.range x) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : P y = 0 := by
        have : y ∈ LinearMap.ker (P.restrictScalars ℝ) := hle ▸ Submodule.mem_top
        simpa using this
      rw [hP, sub_eq_zero] at hy
      have hyeq : y = (A : ℂ)⁻¹ • ∑ i, (((A / a i : ℕ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm y (x i)) • x i := by
        rw [← hy, smul_smul, inv_mul_cancel₀ hA0, one_smul]
      rw [hyeq]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hfin := finrank_range_le_card (R := ℂ) x
    unfold Set.finrank at hfin
    rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at hfin
    omega
  obtain ⟨y₀, hy₀, hw₀⟩ := hex
  obtain ⟨w, hwdef⟩ : ∃ w, w = P y₀ := ⟨_, rfl⟩
  rw [← hwdef] at hw₀
  have hwL : w ∈ S.La := hwdef ▸ hPL y₀ hy₀
  have hPw : P w = (A : ℂ) • w := by rw [hwdef, hPidem]
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hAq
  have hst' : (s : ℂ) * A + t * q = 1 := by exact_mod_cast hst
  have hqinv : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq0
  have hpow : ∀ n : ℕ, ((q : ℂ) ^ n)⁻¹ • w ∈ S.La := by
    intro n
    induction n with
    | zero => simpa using hwL
    | succ n ih =>
      have h₁ : ((q : ℂ)⁻¹ * ((q : ℂ) ^ n)⁻¹ * A) • w ∈ S.La := by
        have h := hdivL _ ih
        rwa [LinearMap.map_smul, hPw, smul_smul, smul_smul] at h
      have key : ((q : ℂ) ^ (n + 1))⁻¹ • w = (s : ℂ) • (((q : ℂ)⁻¹ * ((q : ℂ) ^ n)⁻¹ * A) • w)
          + (t : ℂ) • (((q : ℂ) ^ n)⁻¹ • w) := by
        rw [smul_smul, smul_smul, ← add_smul]
        congr 1
        rw [pow_succ, mul_inv]
        linear_combination (-((q : ℂ) ^ n)⁻¹ * (q : ℂ)⁻¹) * hst' + (t * ((q : ℂ) ^ n)⁻¹) * hqinv
      rw [key, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact S.La.add_mem (S.La.smul_mem s h₁) (S.La.smul_mem t ih)
  obtain ⟨m, hm, hmw⟩ := exists_pos_nat_beta_self_eq hd hH hw₀ (hint _ hwL _ hwL)
  have hqm : ((q : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hq0
  have hne : ((q : ℂ) ^ m)⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero hqm) hw₀
  obtain ⟨n', hn', hnw'⟩ := exists_pos_nat_beta_self_eq hd hH hne (hint _ (hpow m) _ (hpow m))
  rw [_root_.GlobalTheory.MomOne.OrthFrame.beta_smul_left, beta_smul_right' S.d hH.1, hmw, map_inv₀, map_pow,
    Complex.conj_natCast] at hnw'
  have hmC : (m : ℂ) = n' * (q : ℂ) ^ (2 * m) := by
    rw [← hnw']
    field_simp
    ring
  have hnat : m = n' * q ^ (2 * m) := by exact_mod_cast hmC
  have h₁ : q ^ (2 * m) ≤ m := le_of_le_of_eq (Nat.le_mul_of_pos_left _ hn') hnat.symm
  have h₂ : m < q ^ (2 * m) :=
    lt_of_lt_of_le (Nat.lt_pow_self hq.one_lt) (Nat.pow_le_pow_right hq.pos (by omega))
  omega

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in

theorem _root_.GlobalTheory.MomOne.exists_orthFrame : ∀ (q g : ℕ) (S : _root_.Formalism.L2.Ker.JMB.Setup g),
    q.Prime → S.Ok → ¬ q ∣ S.d → ∃ (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), (∀ i, x i ∈ S.La) ∧
      (∀ i j, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) ∧
      ∀ i, 0 < a i ∧ Nat.Coprime (a i) q := by
  intro q g S hq hS hqd
  have hH : S.Hm.IsHermitian := hS.2.2.1.1
  suffices h : ∀ r ≤ g, ∃ (x : Fin r → Fin g → ℂ) (a : Fin r → ℕ), (∀ i, x i ∈ S.La) ∧
      (∀ i j, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) ∧
      ∀ i, 0 < a i ∧ Nat.Coprime (a i) q from h g le_rfl
  intro r hr
  induction r with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨x, a, hx, horth, ha⟩ := ih (by omega)
    obtain ⟨w, hw, hwo, n, hn, hnq, hnw⟩ :=
      exists_orthogonal_vector_norm_coprime hq S hS hqd (by omega) x a hx horth ha
    refine ⟨Fin.snoc (α := fun _ => Fin g → ℂ) x w, Fin.snoc (α := fun _ => ℕ) a n, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hw
      · simpa using hx i
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hnw
      · simp [hwo, (Fin.castSucc_lt_last j).ne']
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← conj_beta_eq_beta_swap _ hH, hwo, map_zero, if_neg (Fin.castSucc_lt_last i).ne]
      · simp [horth]
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using ⟨hn, hnq⟩
      · simpa using ha i
