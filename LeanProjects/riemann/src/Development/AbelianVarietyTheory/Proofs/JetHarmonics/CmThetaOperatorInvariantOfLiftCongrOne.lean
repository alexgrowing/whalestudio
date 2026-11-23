import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators ComplexOrder

namespace GlobalTheory.MomOne.LiftChange

variable {g : ℕ}

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (x y : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.hf Hm (a • x) y = a * _root_.Formalism.L2.Ker.JMB.hf Hm x y := by
  unfold _root_.Formalism.L2.Ker.JMB.hf
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.hf_smul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (x y : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.hf Hm x (a • y) = conj a * _root_.Formalism.L2.Ker.JMB.hf Hm x y := by
  unfold _root_.Formalism.L2.Ker.JMB.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.hf_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x x' y : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.hf Hm (x + x') y = _root_.Formalism.L2.Ker.JMB.hf Hm x y + _root_.Formalism.L2.Ker.JMB.hf Hm x' y := by
  unfold _root_.Formalism.L2.Ker.JMB.hf
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.hf_sum_left (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (x : Fin r → Fin g → ℂ)
    (y : Fin g → ℂ) :
    _root_.Formalism.L2.Ker.JMB.hf Hm (∑ i, x i) y = ∑ i, _root_.Formalism.L2.Ker.JMB.hf Hm (x i) y := by
  unfold _root_.Formalism.L2.Ker.JMB.hf
  simp only [Finset.sum_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.kap_eq_one (Hm : Matrix (Fin g) (Fin g) ℂ)
    (x y : Fin g → ℂ) (z : ℤ) (h : (_root_.Formalism.L2.Ker.JMB.hf Hm x y).im = z) :
    _root_.Formalism.L2.Ker.JMB.kap Hm x y = 1 := by
  unfold _root_.Formalism.L2.Ker.JMB.kap
  rw [h, Complex.exp_eq_one_iff]
  exact ⟨-z, by push_cast; ring⟩

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.norm_int {d : ℕ} (hd : d % 4 = 3) {eps : ℂ}
    (h : eps ∈ _root_.Formalism.L2.Ker.JMB.OK d) :
    eps ∈ _root_.Formalism.L2.Ker.JMB.Qbar ∧ conj eps ∈ _root_.Formalism.L2.Ker.JMB.Qbar ∧ ∃ N : ℤ, eps * conj eps = N := by
  unfold _root_.Formalism.L2.Ker.JMB.OK at h
  obtain ⟨u, v, rfl⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hs : ((√((4 * k + 3 : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 = 4 * (k : ℂ) + 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  have hw : _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) = (1 + Complex.I * (√((4 * k + 3 : ℕ) : ℝ) : ℂ)) / 2 := by
    unfold _root_.Formalism.L2.Ker.JMB.w0 _root_.Formalism.L2.Ker.JMB.rtd
    rfl
  have hconj : conj (_root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3)) = 1 - _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) := by
    rw [hw]
    simp only [map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  have hquad : _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) ^ 2 - _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) + ((k : ℂ) + 1) = 0 := by
    rw [hw]
    linear_combination ((√((4 * k + 3 : ℕ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + (-1 / 4 : ℂ) * hs
  have halg : _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) ∈ _root_.Formalism.L2.Ker.JMB.Qbar := by
    unfold _root_.Formalism.L2.Ker.JMB.Qbar
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℚ) + 1), ?_, ?_⟩
    · intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_zero] at this
      linarith [(Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
    · simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      push_cast
      linear_combination hquad
  have hmem : ∀ a b : ℤ, (a : ℂ) + (b : ℂ) * _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) ∈ _root_.Formalism.L2.Ker.JMB.Qbar := fun a b =>
    add_mem (intCast_mem _ a) (mul_mem (intCast_mem _ b) halg)
  refine ⟨hmem u v, ?_, ⟨u ^ 2 + u * v + v ^ 2 * ((k : ℤ) + 1), ?_⟩⟩
  · have : conj ((u : ℂ) + (v : ℂ) * _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3)) =
        ((u + v : ℤ) : ℂ) + ((-v : ℤ) : ℂ) * _root_.Formalism.L2.Ker.JMB.w0 (4 * k + 3) := by
      rw [map_add, map_mul, hconj]
      simp only [map_intCast]
      push_cast
      ring
    rw [this]
    exact hmem _ _
  · rw [map_add, map_mul, hconj]
    simp only [map_intCast]
    push_cast
    linear_combination (-(v : ℂ) ^ 2) * hquad

open scoped ComplexConjugate BigOperators ComplexOrder in
variable {g : ℕ} in
theorem _root_.GlobalTheory.MomOne.LiftChange.smul_mem (S : _root_.Formalism.L2.Ker.JMB.Setup g) (hS : S.Ok) {a : ℂ}
    (ha : a ∈ _root_.Formalism.L2.Ker.JMB.OK S.d) {x : Fin g → ℂ} (hx : x ∈ S.La) :
    a • x ∈ S.La := by
  obtain ⟨-, -, -, -, -, hw, -⟩ := hS
  unfold _root_.Formalism.L2.Ker.JMB.OK at ha
  obtain ⟨u, v, rfl⟩ := ha
  rw [add_smul, mul_smul]
  refine add_mem ?_ ?_
  · rw [show ((u : ℂ) • x) = u • x from (Int.cast_smul_eq_zsmul ℂ u x)]
    exact S.La.smul_mem u hx
  · rw [show ((v : ℂ) • (_root_.Formalism.L2.Ker.JMB.w0 S.d • x)) = v • (_root_.Formalism.L2.Ker.JMB.w0 S.d • x) from
      (Int.cast_smul_eq_zsmul ℂ v _)]
    exact S.La.smul_mem v (hw x hx)

end GlobalTheory.MomOne.LiftChange

namespace GlobalTheory.MomOne
open LiftChange

open scoped ComplexConjugate BigOperators ComplexOrder in

theorem _root_.GlobalTheory.MomOne.lift_change : ∀ (q : ℕ) [Fact q.Prime] (lam : _root_.Formalism.L2.Ker.JMB.Qbar →+* ℂ_[q]) (g : ℕ) (S : _root_.Formalism.L2.Ker.JMB.Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (n m s : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), S.Ok → (∀ i, b i ∈ S.La) → S.IsTheta e → _root_.Formalism.L2.Ker.JMB.IsIdem lam S.d m eps → 2 * n ≤ m → (∀ i, ∃ z : ℤ, (_root_.Formalism.L2.Ker.JMB.hf S.Hm (eps • b i) t).im = z) → s ≡ 1 [MOD q ^ n] → _root_.Formalism.L2.Ker.JMB.opW S.d S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.opU S.Hm t e) = _root_.Formalism.L2.Ker.JMB.opW S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.opU S.Hm t e) ∧ ∀ v ∈ S.La, _root_.Formalism.L2.Ker.JMB.kap S.Hm v ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) = _root_.Formalism.L2.Ker.JMB.kap S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
  intro q _ lam g S r b e t n m s eps y hS hb he hid hnm hti hs
  obtain ⟨hprime, hd16, hpos, -, -, -, hbeta, -⟩ := id hS
  have hd3 : S.d % 4 = 3 := by omega
  have hdpos : (0 : ℝ) < S.d := by exact_mod_cast hprime.pos
  have hsqrt : (0 : ℝ) < √(S.d : ℝ) := Real.sqrt_pos.2 hdpos
  have hw0 : _root_.Formalism.L2.Ker.JMB.w0 S.d = (1 + Complex.I * (√(S.d : ℝ) : ℂ)) / 2 := by
    unfold _root_.Formalism.L2.Ker.JMB.w0 _root_.Formalism.L2.Ker.JMB.rtd
    rfl
  have hconjhf : ∀ x w : Fin g → ℂ, conj (_root_.Formalism.L2.Ker.JMB.hf S.Hm x w) = _root_.Formalism.L2.Ker.JMB.hf S.Hm w x := by
    intro x w
    unfold _root_.Formalism.L2.Ker.JMB.hf
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show conj (S.Hm j i) = S.Hm i j from hpos.1.apply i j]
    ring
  have hOKim : ∀ {u u' : ℤ}, ((u : ℂ) + (u' : ℂ) * _root_.Formalism.L2.Ker.JMB.w0 S.d).im = u' * (√(S.d : ℝ) / 2) := by
    intro u u'
    rw [hw0]
    simp [Complex.add_im, Complex.mul_im, Complex.div_im]
  have hbetaim : ∀ x w, (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm x w).im = √(S.d : ℝ) / 2 * (_root_.Formalism.L2.Ker.JMB.hf S.Hm x w).im := by
    intro x w
    unfold _root_.Formalism.L2.Ker.JMB.beta
    rw [Complex.im_ofReal_mul]
  have himLa : ∀ v ∈ S.La, ∀ w ∈ S.La, ∃ z : ℤ, (_root_.Formalism.L2.Ker.JMB.hf S.Hm v w).im = z := by
    intro v hv w hw
    obtain ⟨u, u', hu⟩ := hbeta v hv w hw
    refine ⟨u', ?_⟩
    have h1 := congrArg Complex.im hu
    rw [hbetaim, hOKim] at h1
    have hne : √(S.d : ℝ) / 2 ≠ 0 := by positivity
    field_simp at h1
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (s : ℤ) - 1 = (q : ℤ) ^ n * c := by
    have := Nat.modEq_iff_dvd.1 hs.symm
    push_cast at this
    exact this
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqn : ((q : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hqpos.ne')
  have hcC : (s : ℂ) - 1 = (q : ℂ) ^ n * c := by exact_mod_cast hc
  have hYB : _root_.Formalism.L2.Ker.JMB.liftY q n eps b y = (eps / (q : ℂ) ^ n) • ∑ i, (((y i : ℕ)) : ℂ) • b i := rfl
  have hBLa : (∑ i, (((y i : ℕ)) : ℂ) • b i) ∈ S.La := Submodule.sum_mem _ fun i _ => by
    rw [Nat.cast_smul_eq_nsmul ℂ]
    exact nsmul_mem (hb i) _
  have hepsB : eps • (∑ i, (((y i : ℕ)) : ℂ) • b i) ∈ S.La :=
    _root_.GlobalTheory.MomOne.LiftChange.smul_mem S hS hid.1 hBLa
  have hx : ((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y = (c : ℂ) • (eps • ∑ i, (((y i : ℕ)) : ℂ) • b i) := by
    rw [hYB, smul_smul, smul_smul, hcC]
    congr 1
    field_simp
  have hxLa : ((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y ∈ S.La := by
    rw [hx, Int.cast_smul_eq_zsmul ℂ]
    exact S.La.smul_mem c hepsB
  have hsconj : conj (s : ℂ) = s := Complex.conj_natCast s
  have hs1conj : conj ((s : ℂ) - 1) = (s : ℂ) - 1 := by rw [map_sub, hsconj, map_one]
  refine ⟨?_, fun v hv => ?_⟩
  ·
    obtain ⟨hepsQ, hconjQ, N, hN⟩ := _root_.GlobalTheory.MomOne.LiftChange.norm_int hd3 hid.1
    have hdivN : ((q : ℤ) ^ n) ∣ N := by
      obtain ⟨-, h1, h2⟩ := hid
      unfold _root_.Formalism.L2.Ker.JMB.lamA at h1 h2
      rw [dif_pos hepsQ] at h1
      rw [dif_pos hconjQ] at h2
      have hle1 : ‖lam ⟨eps, hepsQ⟩‖ ≤ 1 := by
        have h3 := IsUltrametricDist.norm_add_le_max (lam ⟨eps, hepsQ⟩ - 1) 1
        rw [sub_add_cancel, norm_one] at h3
        refine h3.trans (max_le (h1.trans ?_) le_rfl)
        exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt.le) (by simp)
      have hprod : lam ⟨eps, hepsQ⟩ * lam ⟨conj eps, hconjQ⟩ = (N : ℂ_[q]) := by
        rw [← map_mul]
        have : (⟨eps, hepsQ⟩ * ⟨conj eps, hconjQ⟩ : _root_.Formalism.L2.Ker.JMB.Qbar) = (N : _root_.Formalism.L2.Ker.JMB.Qbar) :=
          Subtype.ext (by simp [hN])
        rw [this, map_intCast]
      have hNn : ‖(N : ℂ_[q])‖ ≤ (q : ℝ) ^ (-(m : ℤ)) := by
        rw [← hprod, norm_mul]
        calc ‖lam ⟨eps, hepsQ⟩‖ * ‖lam ⟨conj eps, hconjQ⟩‖ ≤ 1 * (q : ℝ) ^ (-(m : ℤ)) :=
              mul_le_mul hle1 h2 (norm_nonneg _) zero_le_one
          _ = (q : ℝ) ^ (-(m : ℤ)) := one_mul _
      have hcast : ‖(N : ℂ_[q])‖ = ‖(N : ℚ_[q])‖ := by
        rw [← PadicComplex.norm_extends' q (N : ℚ_[q]), map_intCast]
        congr 1
        first
        | exact (map_intCast (UniformSpace.Completion.coeRingHom (α := PadicAlgCl q)) N).symm
        | norm_cast
        | simp
      rw [hcast] at hNn
      have hm := (Padic.norm_int_le_pow_iff_dvd N m).1 hNn
      exact (pow_dvd_pow (q : ℤ) (by omega : n ≤ m)).trans hm
    obtain ⟨N', hN'⟩ := hdivN

    obtain ⟨u, u', hu⟩ := hbeta _ hBLa _ hBLa
    have hfBB : (_root_.Formalism.L2.Ker.JMB.hf S.Hm (∑ i, (((y i : ℕ)) : ℂ) • b i) (∑ i, (((y i : ℕ)) : ℂ) • b i)).im = 0 :=
      Complex.conj_eq_iff_im.1 (hconjhf _ _)
    have hu' : u' = 0 := by
      have h1 := congrArg Complex.im hu
      rw [hbetaim, hOKim, hfBB, mul_zero] at h1
      have hne : √(S.d : ℝ) / 2 ≠ 0 := by positivity
      have : (u' : ℝ) = 0 := by
        rcases mul_eq_zero.1 h1.symm with h | h
        · exact h
        · exact absurd h hne
      exact_mod_cast this
    have hBu : ((√(S.d : ℝ) / 2 : ℝ) : ℂ) *
        _root_.Formalism.L2.Ker.JMB.hf S.Hm (∑ i, (((y i : ℕ)) : ℂ) • b i) (∑ i, (((y i : ℕ)) : ℂ) • b i) = (u : ℂ) := by
      have h1 := hu
      unfold _root_.Formalism.L2.Ker.JMB.beta at h1
      rw [h1, hu']
      simp
    have hβY : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        (((N * u : ℤ) : ℝ) / ((q : ℝ) ^ n) ^ 2 : ℝ) := by
      unfold _root_.Formalism.L2.Ker.JMB.beta
      rw [hYB, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_left, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, map_div₀, map_pow,
        Complex.conj_natCast]
      have : ((√(S.d : ℝ) / 2 : ℝ) : ℂ) * (eps / (q : ℂ) ^ n * (conj eps / (q : ℂ) ^ n *
          _root_.Formalism.L2.Ker.JMB.hf S.Hm (∑ i, (((y i : ℕ)) : ℂ) • b i) (∑ i, (((y i : ℕ)) : ℂ) • b i))) =
          (eps * conj eps) * (((√(S.d : ℝ) / 2 : ℝ) : ℂ) *
          _root_.Formalism.L2.Ker.JMB.hf S.Hm (∑ i, (((y i : ℕ)) : ℂ) • b i) (∑ i, (((y i : ℕ)) : ℂ) • b i)) /
            ((q : ℂ) ^ n) ^ 2 := by ring
      rw [this, hN, hBu]
      push_cast
      ring
    have hρ : (((_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re : ℝ) : ℂ) =
        _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
      rw [hβY, Complex.ofReal_re]
    have hK2 : ((s : ℂ) - 1) *
        (((_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re : ℝ) : ℂ) =
        ((c * N' * u : ℤ) : ℂ) := by
      rw [hρ, hβY, hcC, hN']
      push_cast
      field_simp

    choose zf hzf using hti
    have hFt : _root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t =
        (c : ℂ) * ∑ i, (((y i : ℕ)) : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm (eps • b i) t := by
      rw [hx, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_left, Finset.smul_sum, _root_.GlobalTheory.MomOne.LiftChange.hf_sum_left]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_left]
    have hFim : (_root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t).im =
        ((c * ∑ i, ((y i : ℕ) : ℤ) * zf i : ℤ) : ℝ) := by
      rw [hFt]
      simp [Complex.mul_im, Complex.im_sum, hzf]
    have hFsub : _root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t -
        conj (_root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t) =
        2 * Complex.I * ((c * ∑ i, ((y i : ℕ) : ℤ) * zf i : ℤ) : ℂ) := by
      rw [Complex.sub_conj, hFim]
      push_cast
      ring
    have hf1 : ∀ z : Fin g → ℂ, _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + (s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t =
        _root_.Formalism.L2.Ker.JMB.hf S.Hm z t + (s : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t := fun z => by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_add_left, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_left]
    have hf2 : ∀ z : Fin g → ℂ, _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t =
        _root_.Formalism.L2.Ker.JMB.hf S.Hm z t + _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t := fun z =>
      _root_.GlobalTheory.MomOne.LiftChange.hf_add_left _ _ _ _
    have hf3 : ∀ z : Fin g → ℂ, _root_.Formalism.L2.Ker.JMB.hf S.Hm z ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        (s : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm z (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := fun z => by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hsconj]
    have hf4 : _root_.Formalism.L2.Ker.JMB.hf S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        (s : ℂ) * ((s : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)) := by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_left, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hsconj]
    have hf5 : ∀ z : Fin g → ℂ, _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t)
        (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) = ((s : ℂ) - 1) *
        (_root_.Formalism.L2.Ker.JMB.hf S.Hm z (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) +
          _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) +
          _root_.Formalism.L2.Ker.JMB.hf S.Hm t (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)) := fun z => by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hs1conj, _root_.GlobalTheory.MomOne.LiftChange.hf_add_left, _root_.GlobalTheory.MomOne.LiftChange.hf_add_left]
    have hf6 : _root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)
        (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) = ((s : ℂ) - 1) * (((s : ℂ) - 1) *
          _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)) := by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_left, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hs1conj]
    have hre1 : (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)
        ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re =
        (s : ℝ) * s * (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re := by
      have : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
          (((s : ℝ) * s : ℝ) : ℂ) * _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
        unfold _root_.Formalism.L2.Ker.JMB.beta
        rw [hf4]
        push_cast
        ring
      rw [this, Complex.re_ofReal_mul]
    have hre2 : (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)
        (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re = ((s : ℝ) - 1) * ((s : ℝ) - 1) *
          (_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re := by
      have : _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)
          (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) = ((((s : ℝ) - 1) * ((s : ℝ) - 1) : ℝ) : ℂ) *
            _root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
        unfold _root_.Formalism.L2.Ker.JMB.beta
        rw [hf6]
        push_cast
        ring
      rw [this, Complex.re_ofReal_mul]
    have hF : ((s : ℂ) - 1) * _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t =
        _root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t :=
      (_root_.GlobalTheory.MomOne.LiftChange.hf_smul_left _ _ _ _).symm
    have hFc : ((s : ℂ) - 1) * _root_.Formalism.L2.Ker.JMB.hf S.Hm t (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        conj (_root_.Formalism.L2.Ker.JMB.hf S.Hm (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t) := by
      rw [hconjhf, _root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hs1conj]
    push_cast at hK2 hFsub
    funext z
    have hθ := congrFun (he.2 _ hxLa) (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t)
    unfold _root_.Formalism.L2.Ker.JMB.opW _root_.Formalism.L2.Ker.JMB.opU at hθ ⊢
    have hpt : z + (s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t =
        (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t) + ((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y := by module
    rw [hpt]
    have hew : e (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t + ((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        e (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t) *
          Complex.exp (-(↑Real.pi * Complex.I * ↑(_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re)) *
          Complex.exp (-(-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t)
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) - ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y))) := by
      rw [← hθ, Complex.exp_neg, Complex.exp_neg]
      field_simp
    rw [hew]
    have key : Complex.exp (↑Real.pi * Complex.I * ↑(_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm
          ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re +
        -(↑Real.pi * Complex.I * ↑(_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re) +
        -(-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t)
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) - ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm
            (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)) +
        (-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + (s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t -
          ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm t t) +
        (-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm z ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) -
          ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)
            ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y))) =
        Complex.exp (↑Real.pi * Complex.I *
          ↑(_root_.Formalism.L2.Ker.JMB.beta S.d S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).re +
        (-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) t - ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm t t) +
        (-↑Real.pi * _root_.Formalism.L2.Ker.JMB.hf S.Hm z (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) -
          ↑Real.pi / 2 * _root_.Formalism.L2.Ker.JMB.hf S.Hm (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y))) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨c * N' * u - c * ∑ i, ((y i : ℕ) : ℤ) * zf i, ?_⟩
      rw [hre1, hre2, hf1, hf2, hf3, hf4, hf5, hf6]
      push_cast
      linear_combination (2 * ↑Real.pi * Complex.I) * hK2 + ↑Real.pi * hFc - ↑Real.pi * hF -
        ↑Real.pi * hFsub
    simp only [Complex.exp_add] at key
    linear_combination (e (z + _root_.Formalism.L2.Ker.JMB.liftY q n eps b y + t)) * key
  · unfold _root_.Formalism.L2.Ker.JMB.kap
    rw [Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨z, hz⟩ := himLa v hv _ hxLa
    have h1 : _root_.Formalism.L2.Ker.JMB.hf S.Hm v ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        (s : ℂ) * _root_.Formalism.L2.Ker.JMB.hf S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hsconj]
    have h2 : _root_.Formalism.L2.Ker.JMB.hf S.Hm v (((s : ℂ) - 1) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y) =
        ((s : ℂ) - 1) * _root_.Formalism.L2.Ker.JMB.hf S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y) := by
      rw [_root_.GlobalTheory.MomOne.LiftChange.hf_smul_right, hs1conj]
    have ha : ((s : ℝ) - 1) * (_root_.Formalism.L2.Ker.JMB.hf S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).im = z := by
      rw [← hz, h2]
      simp [Complex.mul_im]
    have hsv : (_root_.Formalism.L2.Ker.JMB.hf S.Hm v ((s : ℂ) • _root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).im =
        s * (_root_.Formalism.L2.Ker.JMB.hf S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).im := by
      rw [h1]
      simp [Complex.mul_im]
    refine ⟨-z, ?_⟩
    rw [hsv]
    have ha' : ((s : ℂ) - 1) * ((_root_.Formalism.L2.Ker.JMB.hf S.Hm v (_root_.Formalism.L2.Ker.JMB.liftY q n eps b y)).im : ℂ) = (z : ℂ) := by
      exact_mod_cast ha
    push_cast
    linear_combination (-(2 * ↑Real.pi * Complex.I)) * ha'

end GlobalTheory.MomOne
