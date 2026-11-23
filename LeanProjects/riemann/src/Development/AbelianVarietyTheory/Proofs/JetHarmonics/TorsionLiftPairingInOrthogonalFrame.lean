import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.FramePair

variable {g : ℕ}

lemma beta_sum_left (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (c : Fin r → ℂ) (b : Fin r → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ j, c j • b j) w = ∑ j, c j * beta d Hm (b j) w := by
  simp only [beta, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma beta_smul_left (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (v w : Fin g → ℂ) :
    beta d Hm (c • v) w = c * beta d Hm v w := by
  simp only [beta, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {q : ℕ} [Fact q.Prime]

lemma norm_zc (a : ℤ_[q]) : ‖GlobalTheory.MomOne.zc a‖ = ‖a‖ := by
  rw [GlobalTheory.MomOne.zc, norm_algebraMap']; rfl

end GlobalTheory.MomOne.FramePair

namespace GlobalTheory.MomOne
open FramePair

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma hf_eq_dotProduct_mulVec_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.hf Hm u v = u ⬝ᵥ Hm *ᵥ star v := by
  unfold _root_.Formalism.L2.Ker.JMB.hf
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_smul_left' {g d : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (u v : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm (c • u) v = c * _root_.Formalism.L2.Ker.JMB.beta d Hm u v := by
  unfold _root_.Formalism.L2.Ker.JMB.beta; simp only [hf_eq_dotProduct_mulVec_star, smul_dotProduct, smul_eq_mul]; ring

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_add_left' {g d : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u w v : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm (u + w) v = _root_.Formalism.L2.Ker.JMB.beta d Hm u v + _root_.Formalism.L2.Ker.JMB.beta d Hm w v := by
  unfold _root_.Formalism.L2.Ker.JMB.beta; simp only [hf_eq_dotProduct_mulVec_star, add_dotProduct]; ring

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_sum_left' {g d : ℕ} {κ : Type*} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Finset κ)
    (f : κ → Fin g → ℂ) (v : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm (∑ k ∈ t, f k) v = ∑ k ∈ t, _root_.Formalism.L2.Ker.JMB.beta d Hm (f k) v := by
  classical
  induction t using Finset.induction_on with
  | empty => unfold _root_.Formalism.L2.Ker.JMB.beta; simp [hf_eq_dotProduct_mulVec_star]
  | insert k t hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, beta_add_left', ih]

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_swap_eq_conj_of_isHermitian {g d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (u v : Fin g → ℂ) : _root_.Formalism.L2.Ker.JMB.beta d Hm v u = starRingEnd ℂ (_root_.Formalism.L2.Ker.JMB.beta d Hm u v) := by
  unfold _root_.Formalism.L2.Ker.JMB.beta
  rw [map_mul, Complex.conj_ofReal, hf_eq_dotProduct_mulVec_star, hf_eq_dotProduct_mulVec_star]
  congr 1
  have := _root_.GlobalTheory.SiegelNormalForm.form_conj hH u v
  exact this.symm

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_add_right_jet_harmonics {g d : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v w : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm u (v + w) = _root_.Formalism.L2.Ker.JMB.beta d Hm u v + _root_.Formalism.L2.Ker.JMB.beta d Hm u w := by
  unfold _root_.Formalism.L2.Ker.JMB.beta; simp only [hf_eq_dotProduct_mulVec_star, star_add, Matrix.mulVec_add, dotProduct_add]; ring

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_sum_right_jet_harmonics {g d : ℕ} {κ : Type*} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Finset κ)
    (u : Fin g → ℂ) (f : κ → Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm u (∑ k ∈ t, f k) = ∑ k ∈ t, _root_.Formalism.L2.Ker.JMB.beta d Hm u (f k) := by
  classical
  induction t using Finset.induction_on with
  | empty => unfold _root_.Formalism.L2.Ker.JMB.beta; simp [hf_eq_dotProduct_mulVec_star]
  | insert k t hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, beta_add_right_jet_harmonics, ih]

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma beta_smul_right_eq_conj_mul {g d : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (u v : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.beta d Hm u (c • v) = starRingEnd ℂ c * _root_.Formalism.L2.Ker.JMB.beta d Hm u v := by
  unfold _root_.Formalism.L2.Ker.JMB.beta
  simp only [hf_eq_dotProduct_mulVec_star, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RCLike.star_def]
  ring

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in
private lemma eq_sum_beta_div_smul_of_beta_orthogonal {g d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : Hm.PosDef) (hd : 0 < d) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (ha : ∀ i, 0 < a i)
    (hx : ∀ i j, _root_.Formalism.L2.Ker.JMB.beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (v : Fin g → ℂ) :
    v = ∑ i, (_root_.Formalism.L2.Ker.JMB.beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  have hli : LinearIndependent ℂ x := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h := congrArg (fun w => _root_.Formalism.L2.Ker.JMB.beta d Hm w (x i)) hc
    simp only [beta_sum_left', beta_smul_left', hx, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h0 : _root_.Formalism.L2.Ker.JMB.beta d Hm 0 (x i) = 0 := by
      simpa using beta_smul_left' (d := d) Hm 0 (x i) (x i)
    rw [h0] at h
    exact (mul_eq_zero.1 h).resolve_right (ha' i)
  have hspan : Submodule.span ℂ (Set.range x) = ⊤ := hli.span_eq_top_of_card_eq_finrank' (by simp)
  set w := v - ∑ i, (_root_.Formalism.L2.Ker.JMB.beta d Hm v (x i) / (a i : ℂ)) • x i with hw
  have horth : ∀ j, _root_.Formalism.L2.Ker.JMB.beta d Hm w (x j) = 0 := by
    intro j
    have hsub : w + ∑ i, (_root_.Formalism.L2.Ker.JMB.beta d Hm v (x i) / (a i : ℂ)) • x i = v := by rw [hw]; abel
    have := congrArg (fun u => _root_.Formalism.L2.Ker.JMB.beta d Hm u (x j)) hsub
    simp only [beta_add_left', beta_sum_left', beta_smul_left', hx,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, div_mul_cancel₀ _ (ha' j)] at this
    linear_combination this
  have hww : _root_.Formalism.L2.Ker.JMB.beta d Hm w w = 0 := by
    have hmem : w ∈ Submodule.span ℂ (Set.range x) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    conv_lhs => arg 4; rw [← hc]
    rw [beta_sum_right_jet_harmonics]
    simp [beta_smul_right_eq_conj_mul, horth]
  have hw0 : w = 0 := by
    by_contra hne
    have hs : star w ≠ 0 := by simpa using hne
    have hp := hpos.dotProduct_mulVec_pos hs
    rw [star_star] at hp
    unfold _root_.Formalism.L2.Ker.JMB.beta at hww
    rw [hf_eq_dotProduct_mulVec_star] at hww
    have hsq : ((√(d : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < √(d : ℝ) / 2 := by positivity
      exact_mod_cast this.ne'
    have h2 := (mul_eq_zero.1 hww).resolve_left hsq
    rw [h2] at hp
    exact lt_irrefl _ hp
  rw [hw] at hw0
  exact sub_eq_zero.1 hw0

open scoped ComplexConjugate BigOperators in
open Matrix in
open scoped ComplexOrder in

theorem _root_.GlobalTheory.MomOne.kapFrame : ∀ (q : ℕ) [Fact q.Prime] (lam : _root_.Formalism.L2.Ker.JMB.Qbar →+* ℂ_[q])
    (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : _root_.Formalism.L2.Ker.JMB.Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ)
    (b : Fin r → Fin g → ℂ) (n m s s₀ : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)),
    (∀ z : _root_.Formalism.L2.Ker.JMB.Qbar, ι (z : ℂ) = lam z) → S.Ok → _root_.GlobalTheory.MomOne.Split S.d q →
    (∀ i, x i ∈ S.La) → (∀ i j, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) →
    (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → (∀ i, b i ∈ S.La) → _root_.Formalism.L2.Ker.JMB.IsIdem lam S.d m eps →
    2 * n ≤ m → (s₀ * ∏ i, a i) ∣ s →
    let y' : Fin g → ℂ := fun i => _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (x i) / (a i : ℂ);
    (∀ i, _root_.GlobalTheory.MomOne.Good ι S.d n s₀ (y' i)) ∧
      ∀ (A : Fin r → ℤ_[q]) (A' : Fin g → ℤ_[q]),
        (∀ i, _root_.GlobalTheory.MomOne.zc (A' i) =
          ∑ j, _root_.GlobalTheory.MomOne.zc (A j) * ι (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (b j))) →
        _root_.Formalism.L2.Ker.JMB.kap S.Hm (_root_.Formalism.L2.Ker.JMB.vecA n b A) ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) ∈ _root_.Formalism.L2.Ker.JMB.Qbar ∧
          ι (_root_.Formalism.L2.Ker.JMB.kap S.Hm (_root_.Formalism.L2.Ker.JMB.vecA n b A) ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)) =
            ∏ i, ι (_root_.GlobalTheory.MomOne.kap1 S.d 1 (y' i)) ^ (PadicInt.toZModPow n (A' i)).val := by
  intro q _ lam ι g S x a r b n m s s₀ eps y hlam hS hsplit hxL hx ha hbL hidem hnm hdiv y'
  obtain ⟨hd, h7, hpos, -, -, -, hint, -⟩ := hS
  obtain ⟨⟨hO1, -, hring⟩, hint2, hdivq, -, -, hherm, -⟩ :=
    _root_.GlobalTheory.MomOne.okArith S.d q ι hd h7 hsplit
  set O := _root_.GlobalTheory.MomOne.InOK S.d with hOdef
  have hO_add : ∀ u v, O u → O v → O (u + v) := fun u v hu hv => (hring u v hu hv).1
  have hO_mul : ∀ u v, O u → O v → O (u * v) := fun u v hu hv => (hring u v hu hv).2.1
  have hO_neg : ∀ u, O u → O (-u) := fun u hu => (hring u u hu hu).2.2.1
  have hO_conj : ∀ u, O u → O (starRingEnd ℂ u) := fun u hu => (hring u u hu hu).2.2.2
  have hO_sub : ∀ u v, O u → O v → O (u - v) := fun u v hu hv => by
    rw [sub_eq_add_neg]; exact hO_add _ _ hu (hO_neg _ hv)
  have hO_nat : ∀ k : ℕ, O (k : ℂ) := by
    intro k
    induction k with
    | zero => simpa using hO_sub 1 1 hO1 hO1
    | succ k ih => push_cast; exact hO_add _ _ ih hO1
  have hO_sum : ∀ (t : Finset (Fin r)) (f : Fin r → ℂ), (∀ j, O (f j)) → O (∑ j ∈ t, f j) := by
    intro t f hf
    classical
    induction t using Finset.induction_on with
    | empty => simpa using hO_sub 1 1 hO1 hO1
    | insert k t hk ih => rw [Finset.sum_insert hk]; exact hO_add _ _ (hf k) ih
  have hβO : ∀ u ∈ S.La, ∀ v ∈ S.La, O (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u v) := by
    intro u hu v hv
    obtain ⟨p, p', hp⟩ := hint u hu v hv
    refine ⟨p, p', ?_⟩
    rw [hp]
    unfold _root_.Formalism.L2.Ker.JMB.w0 _root_.Formalism.L2.Ker.JMB.rtd _root_.GlobalTheory.MomOne.wK
    ring
  have hnorm1 : ∀ u, O u → ‖ι u‖ ≤ 1 := by
    intro u hu
    obtain ⟨c, hc⟩ := (hint2 u hu).1
    rw [hc, _root_.GlobalTheory.MomOne.OKArith.zc_eq, _root_.GlobalTheory.MomOne.OKArith.norm_zc]
    exact PadicInt.norm_le_one c
  have halg : ∀ u, O u → u ∈ _root_.Formalism.L2.Ker.JMB.Qbar := fun u hu => (hint2 u hu).2.2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).one_lt.le
  have hepsO : O eps := hidem.1
  have heps_conj : ‖ι (starRingEnd ℂ eps)‖ ≤ (q : ℝ) ^ (-(m : ℤ)) := by
    have h := hidem.2.2
    unfold _root_.Formalism.L2.Ker.JMB.lamA at h
    rw [dif_pos (halg _ (hO_conj _ hepsO))] at h
    rw [hlam ⟨_, halg _ (hO_conj _ hepsO)⟩]
    exact h
  have hdi : ∀ i, s₀ * a i ∣ s := fun i =>
    (Nat.mul_dvd_mul_left s₀ (Finset.dvd_prod_of_mem a (Finset.mem_univ i))).trans hdiv
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  set W : Fin g → ℂ := fun i => ∑ k, ((y k : ℕ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (b k) (x i) with hW
  have hWO : ∀ i, O (W i) := fun i =>
    hO_sum _ _ fun k => hO_mul _ _ (hO_nat _) (hβO _ (hbL k) _ (hxL i))
  have hY : ∀ v, _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) v =
      (s : ℂ) * eps / (q : ℂ) ^ n * ∑ k, ((y k : ℕ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (b k) v := by
    intro v
    unfold _root_.Formalism.L2.Ker.JMB.liftY
    rw [beta_smul_left', beta_smul_left', beta_sum_left']
    simp only [beta_smul_left']
    ring
  have hy' : ∀ i, y' i = (s : ℂ) * eps * W i / ((q : ℂ) ^ n * a i) := by
    intro i
    simp only [y', hY, W]
    field_simp
  have hmn : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(2 * (n : ℤ))) :=
    zpow_le_zpow_right₀ hq1 (by omega)
  have hgood : ∀ i, _root_.GlobalTheory.MomOne.Good ι S.d n s₀ (y' i) := by
    intro i
    obtain ⟨c, hc⟩ := hdi i
    refine ⟨(c : ℂ) * eps * W i, hO_mul _ _ (hO_mul _ _ (hO_nat c) hepsO) (hWO i), ?_, ?_⟩
    · rw [map_mul, map_mul, map_mul, map_mul, norm_mul, norm_mul]
      have h1 := hnorm1 _ (hO_conj _ (hO_nat c))
      have h2 := hnorm1 _ (hO_conj _ (hWO i))
      calc ‖ι (starRingEnd ℂ (c : ℂ))‖ * ‖ι (starRingEnd ℂ eps)‖ * ‖ι (starRingEnd ℂ (W i))‖
          ≤ 1 * (q : ℝ) ^ (-(m : ℤ)) * 1 := by gcongr
        _ ≤ _ := by simpa using hmn
    · rw [hy' i, hc, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hq0) (ha0 i)) (pow_ne_zero _ hq0)]
      push_cast
      ring
  refine ⟨hgood, fun A A' hA => ?_⟩
  choose c hc using hdi
  have hqn0 : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ hq0
  have hmn' : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := zpow_le_zpow_right₀ hq1 (by omega)
  have hred : ∀ t : ℤ_[q], ‖_root_.GlobalTheory.MomOne.zc t - ((PadicInt.toZModPow n t).val : ℂ_[q])‖ ≤
      (q : ℝ) ^ (-(n : ℤ)) := by
    intro t
    have hker : t - ((PadicInt.toZModPow n t).val : ℤ_[q]) ∈ RingHom.ker (PadicInt.toZModPow n) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    obtain ⟨w, hw⟩ := hker
    have he : _root_.GlobalTheory.MomOne.zc t - ((PadicInt.toZModPow n t).val : ℂ_[q]) =
        _root_.GlobalTheory.MomOne.OKArith.zcHom q (t - ((PadicInt.toZModPow n t).val : ℤ_[q])) := by
      rw [_root_.GlobalTheory.MomOne.OKArith.zc_eq, map_sub, map_natCast]
    rw [he, _root_.GlobalTheory.MomOne.OKArith.norm_zc, hw, norm_mul, PadicInt.norm_p_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)
  set N : Fin g → ℕ := fun i => (PadicInt.toZModPow n (A' i)).val with hN
  set Nb : Fin r → ℕ := fun j => (PadicInt.toZModPow n (A j)).val with hNb
  set Y := (s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y with hYdef
  set u := _root_.Formalism.L2.Ker.JMB.vecA n b A with hu
  have hu' : u = ∑ j, (Nb j : ℂ) • b j := by
    simp only [hu, _root_.Formalism.L2.Ker.JMB.vecA, Nb, Nat.cast_smul_eq_nsmul]
  set D : Fin g → ℂ := fun i => _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u (x i) - N i with hD
  have huxO : ∀ i, O (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u (x i)) := by
    intro i
    rw [hu', beta_sum_left']
    exact hO_sum _ _ fun j => by
      rw [beta_smul_left']; exact hO_mul _ _ (hO_nat _) (hβO _ (hbL j) _ (hxL i))
  have hDO : ∀ i, O (D i) := fun i => hO_sub _ _ (huxO i) (hO_nat _)
  have hconjD : ∀ i, ‖ι (starRingEnd ℂ (D i))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro i
    have h1 : starRingEnd ℂ (D i) = ∑ j, (Nb j : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (b j) - N i := by
      simp only [hD, map_sub, map_natCast, ← beta_swap_eq_conj_of_isHermitian hpos.1, hu', beta_sum_right_jet_harmonics,
        beta_smul_right_eq_conj_mul]
    have h2 : ι (starRingEnd ℂ (D i)) = ∑ j, ((Nb j : ℂ_[q]) - _root_.GlobalTheory.MomOne.zc (A j)) *
        ι (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (x i) (b j)) + (_root_.GlobalTheory.MomOne.zc (A' i) - N i) := by
      rw [h1, hA i, map_sub, map_sum, map_natCast]
      simp only [map_mul, map_natCast, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [h2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
      rw [norm_mul]
      have := hnorm1 _ (hβO _ (hxL i) _ (hbL j))
      rw [norm_sub_rev]
      calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * 1 := by gcongr; exact hred (A j)
        _ = _ := mul_one _
    · exact hred (A' i)
  set ζ : Fin g → ℂ := fun i => D i * starRingEnd ℂ (eps * W i) with hζ
  have hζO : ∀ i, O (ζ i / (q : ℂ) ^ n) := by
    intro i
    refine hdivq (ζ i) n (hO_mul _ _ (hDO i) (hO_conj _ (hO_mul _ _ hepsO (hWO i)))) ?_ ?_
    · simp only [hζ, map_mul, norm_mul]
      have h1 := hnorm1 _ (hDO i)
      have h2 := hnorm1 _ (hO_conj _ (hWO i))
      calc _ ≤ 1 * ((q : ℝ) ^ (-(m : ℤ)) * 1) := by gcongr
        _ ≤ _ := by simpa using hmn'
    · simp only [hζ, map_mul, Complex.conj_conj, norm_mul]
      have h2 := hnorm1 _ hepsO
      have h3 := hnorm1 _ (hWO i)
      calc _ ≤ (q : ℝ) ^ (-(n : ℤ)) * (1 * 1) := by gcongr; exact hconjD i
        _ = _ := by ring
  have hexp := eq_sum_beta_div_smul_of_beta_orthogonal hpos hd.pos x a (fun i => (ha i).1) hx Y
  have hβuY : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u Y = ∑ i, starRingEnd ℂ (y' i) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u (x i) := by
    calc _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u Y
        = _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u (∑ i, (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm Y (x i) / (a i : ℂ)) • x i) := congrArg _ hexp
      _ = _ := by
        rw [beta_sum_right_jet_harmonics]
        exact Finset.sum_congr rfl fun i _ => by rw [beta_smul_right_eq_conj_mul]
  have hconjy : ∀ i, starRingEnd ℂ (y' i) * D i = ((c i * s₀ : ℕ) : ℂ) * (ζ i / (q : ℂ) ^ n) := by
    intro i
    have hs : (s : ℂ) = (s₀ : ℂ) * a i * c i := by exact_mod_cast hc i
    have hyi : starRingEnd ℂ (y' i) =
        (s : ℂ) * starRingEnd ℂ eps * starRingEnd ℂ (W i) / ((q : ℂ) ^ n * a i) := by
      rw [hy' i, map_div₀, map_mul, map_mul, map_mul, map_natCast, map_natCast, map_pow, map_natCast]
    rw [hyi, hs]
    show _ = _ * (D i * starRingEnd ℂ (eps * W i) / _)
    simp only [map_mul]
    push_cast
    have hai := ha0 i
    field_simp
    all_goals ring
  have hherm_eq : ∀ z w : ℂ, _root_.GlobalTheory.MomOne.h1 S.d z w =
      ((2 / √(S.d : ℝ) : ℝ) : ℂ) * (z * starRingEnd ℂ w) := fun z w => rfl
  have hkey : _root_.Formalism.L2.Ker.JMB.hf S.Hm u Y = ∑ i, (N i : ℂ) * _root_.GlobalTheory.MomOne.h1 S.d 1 (y' i) +
      ∑ i, _root_.GlobalTheory.MomOne.h1 S.d (((c i * s₀ : ℕ) : ℂ) * (ζ i / (q : ℂ) ^ n)) 1 := by
    have hsq : √(S.d : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hd.pos)).ne'
    have hsd : ((√(S.d : ℝ) / 2 : ℝ) : ℂ) * ((2 / √(S.d : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm, div_self (by positivity)]
      simp
    have hβQ : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u Y = ((√(S.d : ℝ) / 2 : ℝ) : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm u Y := rfl
    simp only [hherm_eq, ← hconjy, map_one, mul_one, one_mul]
    have hsum : ∑ i, (N i : ℂ) * (((2 / √(S.d : ℝ) : ℝ) : ℂ) * starRingEnd ℂ (y' i)) +
        ∑ i, ((2 / √(S.d : ℝ) : ℝ) : ℂ) * (starRingEnd ℂ (y' i) * D i) =
        ((2 / √(S.d : ℝ) : ℝ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm u Y := by
      rw [hβuY, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hD]
      ring
    rw [hsum, hβQ]
    linear_combination (-(_root_.Formalism.L2.Ker.JMB.hf S.Hm u Y)) * hsd
  have hint3 : ∀ i, ∃ k : ℤ,
      (_root_.GlobalTheory.MomOne.h1 S.d (((c i * s₀ : ℕ) : ℂ) * (ζ i / (q : ℂ) ^ n)) 1).im = k :=
    fun i => hherm _ _ (hO_mul _ _ (hO_nat _) (hζO i)) hO1
  choose k hk using hint3
  have hprod : _root_.Formalism.L2.Ker.JMB.kap S.Hm u Y = ∏ i, _root_.GlobalTheory.MomOne.kap1 S.d 1 (y' i) ^ N i := by
    unfold _root_.Formalism.L2.Ker.JMB.kap _root_.GlobalTheory.MomOne.kap1
    rw [hkey, Complex.add_im, Complex.im_sum, Complex.im_sum]
    simp only [hk, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    have h1 : Complex.exp (-(2 * ↑Real.pi * Complex.I) * ↑(∑ i, (k i : ℝ))) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨-∑ i, k i, by push_cast; ring⟩
    rw [h1, mul_one, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmem : ∀ i, _root_.GlobalTheory.MomOne.kap1 S.d 1 (y' i) ∈ _root_.Formalism.L2.Ker.JMB.Qbar := by
    intro i
    have h := _root_.GlobalTheory.MomOne.Basic.cmLatticeCommutatorPairing_pow_eq_one_of_good_lift ι hd.pos (hgood i)
    rw [← map_pow, ← map_one ι] at h
    have h' := ι.injective h
    unfold _root_.Formalism.L2.Ker.JMB.Qbar
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow (pow_pos (Fact.out : q.Prime).pos n) (by rw [h']; exact isIntegral_one)).isAlgebraic
  refine ⟨?_, ?_⟩
  · rw [hprod]
    exact prod_mem fun i _ => pow_mem (hmem i) _
  · rw [hprod, map_prod]
    exact Finset.prod_congr rfl fun i _ => map_pow _ _ _

end GlobalTheory.MomOne
