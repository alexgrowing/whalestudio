import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrimeStatement

open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

namespace GlobalTheory.MomN.GoodLift
open GlobalTheory.MomOne.LiftChange

variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem hf_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) :
    hf Hm x (y + y') = hf Hm x y + hf Hm x y' := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_neg_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) : hf Hm x (-y) = -hf Hm x y := by
  have h := hf_smul_right Hm (-1) x y
  rw [neg_one_smul, map_neg, map_one, neg_one_mul] at h
  exact h

theorem hf_sub_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) :
    hf Hm x (y - y') = hf Hm x y - hf Hm x y' := by
  rw [sub_eq_add_neg, hf_add_right, hf_neg_right, ← sub_eq_add_neg]

theorem hf_sub_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x x' y : Fin g → ℂ) :
    hf Hm (x - x') y = hf Hm x y - hf Hm x' y := by
  rw [sub_eq_add_neg, hf_add_left, ← neg_one_smul ℂ x', hf_smul_left]; ring

theorem hf_sum_right (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (x : Fin g → ℂ) (y : Fin r → Fin g → ℂ) :
    hf Hm x (∑ i, y i) = ∑ i, hf Hm x (y i) := by
  have : ∀ s : Finset (Fin r), hf Hm x (∑ i ∈ s, y i) = ∑ i ∈ s, hf Hm x (y i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_right, ih]
  exact this _

theorem norm_zc (a : ℤ_[q]) : ‖GlobalTheory.MomOne.zc a‖ = ‖a‖ := by
  rw [GlobalTheory.MomOne.zc, norm_algebraMap']; rfl

theorem norm_natCast_le (N : ℕ) : ‖(N : ℂ_[q])‖ ≤ 1 := by
  have : (N : ℂ_[q]) = GlobalTheory.MomOne.zc (N : ℤ_[q]) := by simp [GlobalTheory.MomOne.zc]
  rw [this, norm_zc]; exact PadicInt.norm_le_one _

theorem norm_q_pow (n : ℕ) : ‖(q : ℂ_[q]) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
  rw [norm_pow, this, norm_algebraMap', Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.MomN.GoodLift

namespace GlobalTheory.MomN
open GlobalTheory.MomOne.LiftChange GlobalTheory.MomN.GoodLift
open scoped ComplexOrder

set_option maxHeartbeats 4000000 in

theorem goodLift_eq : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.IsTheta e → ∀ N₀ : ℕ, 0 < N₀ → Nat.Coprime N₀ q → (N₀ : ℂ) • t ∈ S.La → ∀ (n : ℕ), ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ OK S.d, ‖lamA lam (conj κ)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (q : ℂ) ^ n) • x}, (∃ z : ℤ, (beta S.d S.Hm y y).re = z) ∧ ∃ (m : ℕ) (eps : ℂ) (yt : Fin r → Fin (q ^ n)), IsIdem lam S.d m eps ∧ 2 * n ≤ m ∧ (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) ∧ opW S.d S.Hm y (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b yt) (opU S.Hm t e) ∧ ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) y = kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n eps b yt) := by
  intro q _ lam g S r b e t hS hsp hb he N₀ hN₀ hcop hNt n y hy
  have hqp : q.Prime := Fact.out
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_le
  have hd4 : S.d % 4 = 3 := by have := hS.2.1; omega
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending q lam
  obtain ⟨⟨-, -, hcl⟩, hZ, hdiv, hid, -, -, -⟩ := GlobalTheory.MomOne.okArith S.d q ι hS.1 hS.2.1 hsp
  obtain ⟨H1, -, -, H4, H5, H6⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hS.1.pos hS.2.2.1.isHermitian
  have hlam : ∀ x : ℂ, x ∈ Qbar → lamA lam x = ι x := fun x hx => by
    rw [lamA, dif_pos hx]; exact (hι ⟨x, hx⟩).symm
  have hOK1 : ∀ α ∈ OK S.d, ‖ι α‖ ≤ 1 := fun α hα => by
    obtain ⟨⟨a, ha⟩, -⟩ := hZ α hα
    rw [ha, norm_zc]; exact PadicInt.norm_le_one a
  have hbOK : ∀ x ∈ S.La, ∀ y ∈ S.La, beta S.d S.Hm x y ∈ OK S.d := hS.2.2.2.2.2.2.1
  have himI : ∀ x ∈ S.La, ∀ y ∈ S.La, ∃ k : ℤ, (hf S.Hm x y).im = k := fun x hx y hy => by
    obtain ⟨u, v, huv⟩ := hbOK x hx y hy
    exact ⟨v, H5 _ _ _ _ huv⟩
  have hnat : ∀ N : ℕ, ‖ι (N : ℂ)‖ ≤ 1 := fun N => by rw [map_natCast]; exact norm_natCast_le N
  have hnat1 : ∀ N : ℕ, Nat.Coprime N q → ‖ι (N : ℂ)‖ = 1 := fun N h => by
    rw [map_natCast]; exact GlobalTheory.MomOne.Basic.norm_nat_eq_one h.symm
  have hqn : ‖ι ((q : ℂ) ^ n)‖ = (q : ℝ) ^ (-(n : ℤ)) := by rw [map_pow, map_natCast]; exact norm_q_pow n
  have hconjOK : ∀ α ∈ OK S.d, conj α ∈ OK S.d := fun α h => (hcl α α h h).2.2.2
  have hmulOK : ∀ α β, α ∈ OK S.d → β ∈ OK S.d → α * β ∈ OK S.d := fun α β h h' => (hcl α β h h').2.1
  have hnatOK : ∀ N : ℕ, (N : ℂ) ∈ OK S.d := fun N => ⟨N, 0, by simp⟩
  have hconjB : ∀ x y, beta S.d S.Hm y x = conj (beta S.d S.Hm x y) := fun x y => by
    rw [beta, beta, H4 x y, map_mul, Complex.conj_ofReal]
  have hpow_le : (q : ℝ) ^ (-(2 * n : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := zpow_le_zpow_right₀ hq1 (by omega)
  have hpos : ∀ k : ℤ, (0 : ℝ) ≤ (q : ℝ) ^ k := fun k => by positivity
  have bsr : ∀ (a : ℂ) x y, beta S.d S.Hm x (a • y) = conj a * beta S.d S.Hm x y := fun a x y => by
    rw [beta, beta, hf_smul_right]; ring
  have bsl : ∀ (a : ℂ) x y, beta S.d S.Hm (a • x) y = a * beta S.d S.Hm x y := fun a x y => by
    rw [beta, beta, hf_smul_left]; ring
  have bar : ∀ x y y', beta S.d S.Hm x (y + y') = beta S.d S.Hm x y + beta S.d S.Hm x y' := fun x y y' => by
    rw [beta, beta, beta, hf_add_right]; ring
  have bsubr : ∀ x y y', beta S.d S.Hm x (y - y') = beta S.d S.Hm x y - beta S.d S.Hm x y' := fun x y y' => by
    rw [beta, beta, beta, hf_sub_right]; ring
  have bsubl : ∀ x x' y, beta S.d S.Hm (x - x') y = beta S.d S.Hm x y - beta S.d S.Hm x' y := fun x x' y => by
    rw [beta, beta, beta, hf_sub_left]; ring
  have bnr : ∀ x y, beta S.d S.Hm x (-y) = -beta S.d S.Hm x y := fun x y => by
    rw [beta, beta, hf_neg_right]; ring
  have bsumr : ∀ x (y : Fin r → Fin g → ℂ), beta S.d S.Hm x (∑ j, y j) = ∑ j, beta S.d S.Hm x (y j) := fun x y => by
    rw [beta, hf_sum_right, Finset.mul_sum]; rfl
  have bsuml : ∀ (x : Fin r → Fin g → ℂ) y, beta S.d S.Hm (∑ j, x j) y = ∑ j, beta S.d S.Hm (x j) y := fun x y => by
    rw [beta, hf_sum_left, Finset.mul_sum]; rfl
  have usub : ∀ a b : ℂ_[q], ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
    rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)
  have hN0r : conj (N₀ : ℂ) = N₀ := map_natCast _ _
  have hqr : conj ((q : ℂ) ^ n) = (q : ℂ) ^ n := by rw [map_pow, map_natCast]
  have hqnC : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hqp.ne_zero)

  have step1 : ∃ v ∈ S.La, y = ((N₀ : ℂ) / (q : ℂ) ^ n) • v ∧
      ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x v)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy' =>
      obtain ⟨κ, hκ, hκs, x0, hx0, rfl⟩ := hy'
      refine ⟨κ • x0, GlobalTheory.MomOne.LiftChange.smul_mem S hS hκ hx0, by rw [smul_smul]; congr 1; ring, fun x hx => ?_⟩
      rw [bsr, map_mul, norm_mul, ← hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hκ).2.1]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := mul_le_mul hκs (hOK1 _ (hbOK x hx x0 hx0)) (norm_nonneg _) (hpos _)
        _ = _ := mul_one _
    | zero => exact ⟨0, zero_mem _, by simp, fun x hx => by simp [beta, hf]; positivity⟩
    | add y1 y2 _ _ ih1 ih2 =>
      obtain ⟨v1, hv1, rfl, h1⟩ := ih1
      obtain ⟨v2, hv2, rfl, h2⟩ := ih2
      refine ⟨v1 + v2, add_mem hv1 hv2, (smul_add _ _ _).symm, fun x hx => ?_⟩
      rw [bar, map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 x hx) (h2 x hx))
    | neg y1 _ ih =>
      obtain ⟨v1, hv1, rfl, h1⟩ := ih
      refine ⟨-v1, neg_mem hv1, (smul_neg _ _).symm, fun x hx => ?_⟩
      rw [bnr, map_neg, norm_neg]; exact h1 x hx
  obtain ⟨v, hv, rfl, hvs⟩ := step1

  have hre : ∃ z : ℤ, (beta S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (((N₀ : ℂ) / (q : ℂ) ^ n) • v)).re = z := by
    have hα : beta S.d S.Hm v v ∈ OK S.d := hbOK v hv v hv
    have hαc : conj (beta S.d S.Hm v v) = beta S.d S.Hm v v := (hconjB v v).symm
    have hγ : GlobalTheory.MomOne.InOK S.d (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)) :=
      hdiv _ (2 * n) hα (by push_cast; exact hvs v hv) (by rw [hαc]; push_cast; exact hvs v hv)
    obtain ⟨u, w', hu⟩ := hγ
    have hγc : conj (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)) = beta S.d S.Hm v v / (q : ℂ) ^ (2 * n) := by
      rw [map_div₀, hαc, map_pow, map_natCast]
    have hw'0 : w' = 0 := by
      have him := congrArg Complex.im hu
      have hc := congrArg Complex.im hγc
      rw [Complex.conj_im] at hc
      have h0 : (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)).im = 0 := by linarith
      rw [h0] at him
      have hs : Real.sqrt S.d ≠ 0 := by have := hS.1.pos; positivity
      simp [GlobalTheory.MomOne.wK, hs] at him
      exact_mod_cast him
    rw [hw'0, Int.cast_zero, zero_mul, add_zero, div_eq_iff (pow_ne_zero _ (by exact_mod_cast hqp.ne_zero))] at hu
    refine ⟨N₀ ^ 2 * u, ?_⟩
    have : beta S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (((N₀ : ℂ) / (q : ℂ) ^ n) • v) = ((N₀ ^ 2 * u : ℤ) : ℂ) := by
      rw [bsl, bsr, map_div₀, hN0r, hqr, hu]
      push_cast
      field_simp
      ring
    rw [this, Complex.intCast_re]

  obtain ⟨e0, he0, he0a, he0b⟩ := hid (2 * n) N₀ hcop
  have he0' : e0 ∈ OK S.d := he0
  have he0b' : ‖ι (conj e0)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by have := he0b; push_cast at this; exact this
  have he0a' : ‖ι ((N₀ : ℂ) * e0 - 1)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by
    rw [map_sub, map_one]; have := he0a; push_cast at this; exact this
  have hepsOK : (N₀ : ℂ) * e0 ∈ OK S.d := hmulOK _ _ (hnatOK N₀) he0'
  have hidem : IsIdem lam S.d (2 * n) ((N₀ : ℂ) * e0) := by
    refine ⟨hepsOK, ?_, ?_⟩
    · rw [hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hepsOK).1]; exact he0a
    · rw [hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hepsOK).2.1, map_mul, hN0r, map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-((2 * n : ℕ) : ℤ)) := mul_le_mul (hnat N₀) he0b (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have htI : ∀ i, ∃ z : ℤ, (hf S.Hm (((N₀ : ℂ) * e0) • b i) t).im = z := fun i => by
    have : hf S.Hm (((N₀ : ℂ) * e0) • b i) t = hf S.Hm (e0 • b i) ((N₀ : ℂ) • t) := by
      rw [hf_smul_left, hf_smul_left, hf_smul_right, hN0r]; ring
    rw [this]; exact himI _ (GlobalTheory.MomOne.LiftChange.smul_mem S hS he0' (hb.1 i)) _ hNt

  obtain ⟨s, c, hs, hc, hbc, hexp⟩ := GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime q g S r b hS hb
  choose a ha using fun j => (hZ _ (hbOK v hv (c j) (hc j))).1
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero _ hqp.ne_zero⟩
  let A : Fin r → ZMod (q ^ n) := fun j =>
    PadicInt.toZModPow n (a j) * (N₀ : ZMod (q ^ n)) * ((s : ZMod (q ^ n)))⁻¹
  let yt : Fin r → Fin (q ^ n) := fun j => ⟨(A j).val, ZMod.val_lt _⟩
  have hyt : ∀ j, ‖ι ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro j
    have e1 : ι ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ)) =
        GlobalTheory.MomOne.zc ((N₀ : ℤ_[q]) * a j - (s : ℤ_[q]) * ((yt j : ℕ) : ℤ_[q])) := by
      rw [map_sub, map_mul, map_mul, ha j, map_natCast, map_natCast, map_natCast]
      simp [GlobalTheory.MomOne.zc]
    rw [e1, norm_zc, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have hinv : (s : ZMod (q ^ n)) * (s : ZMod (q ^ n))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one s (Nat.Coprime.pow_right n hs)
    have hv' : (((yt j : ℕ)) : ZMod (q ^ n)) = A j := ZMod.natCast_zmod_val (A j)
    simp only [map_sub, map_mul, map_natCast, hv', A]
    linear_combination (-(PadicInt.toZModPow n (a j) * (N₀ : ZMod (q ^ n)))) * hinv

  set B : Fin g → ℂ := ∑ i, ((yt i : ℕ) : ℂ) • b i with hBdef
  have hB : B ∈ S.La := Submodule.sum_mem _ fun i _ => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
  set w := v - e0 • B with hwdef
  have hw : w ∈ S.La := sub_mem hv (GlobalTheory.MomOne.LiftChange.smul_mem S hS he0' hB)
  have hbc' : ∀ i j, beta S.d S.Hm (b i) (c j) = if i = j then (s : ℂ) else 0 := fun i j => by
    rw [hconjB (c j) (b i), hbc]; split_ifs <;> simp
  have hBc : ∀ j, beta S.d S.Hm B (c j) = ((yt j : ℕ) : ℂ) * s := fun j => by
    rw [hBdef, bsuml]
    simp [bsl, hbc']
  have hkey : ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x w)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧
      ‖ι (conj (beta S.d S.Hm x w))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro x hx
    constructor
    · rw [hwdef, bsubr, bsr, map_sub, map_mul]
      refine (usub _ _).trans (max_le (hvs x hx) ?_)
      rw [norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := mul_le_mul he0b' (hOK1 _ (hbOK x hx B hB)) (norm_nonneg _) (hpos _)
        _ = _ := mul_one _
    · rw [← hconjB x w]
      have hsum : (s : ℂ) * beta S.d S.Hm w x =
          ∑ j, beta S.d S.Hm (b j) x * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)) := by
        have h1 : (s : ℂ) * beta S.d S.Hm w x = beta S.d S.Hm w ((s : ℂ) • x) := by rw [bsr, map_natCast]
        rw [h1, hexp x hx, bsumr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [bsr, ← hconjB, hwdef, bsubl, bsl, hBc]
      have hterm : ∀ j, ‖ι (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
        intro j
        have hdecomp : (N₀ : ℂ) * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)) =
            ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ)) -
              ((N₀ : ℂ) * e0 - 1) * (((yt j : ℕ) : ℂ) * s) := by ring
        have h2 : ‖ι (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s))‖ =
            ‖ι ((N₀ : ℂ) * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)))‖ := by
          rw [map_mul, norm_mul, hnat1 N₀ hcop, one_mul]
        rw [h2, hdecomp, map_sub]
        refine (usub _ _).trans (max_le (hyt j) ?_)
        rw [map_mul, norm_mul]
        calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
              mul_le_mul he0a' (by rw [map_mul, norm_mul]; exact mul_le_one₀ (hnat _) (norm_nonneg _) (hnat _))
                (norm_nonneg _) (hpos _)
          _ ≤ _ := by rw [mul_one]; exact hpow_le
      have h3 : ‖ι (beta S.d S.Hm w x)‖ = ‖ι ((s : ℂ) * beta S.d S.Hm w x)‖ := by
        rw [map_mul, norm_mul, hnat1 s hs, one_mul]
      rw [h3, hsum, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun j _ => ?_
      rw [map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-(n : ℤ)) :=
            mul_le_mul (hOK1 _ (hbOK _ (hb.1 j) x hx)) (hterm j) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  set L := ((q : ℂ) ^ n)⁻¹ • w with hLdef
  have hbL : ∀ x, beta S.d S.Hm x L = beta S.d S.Hm x w / (q : ℂ) ^ n := fun x => by
    rw [hLdef, bsr, map_inv₀, hqr, div_eq_inv_mul]
  have hLOK : ∀ x ∈ S.La, beta S.d S.Hm x L ∈ OK S.d := fun x hx => by
    rw [hbL]
    exact hdiv _ n (hbOK x hx w hw) ((hkey x hx).1.trans hpow_le) (hkey x hx).2
  have hL : L ∈ S.La := hS.2.2.2.2.2.2.2 L fun x hx => by
    obtain ⟨u, v', h⟩ := hLOK x hx
    exact ⟨v', H5 _ _ _ _ h⟩
  have hLs : ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x L)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := fun x hx => by
    have h := (hkey x hx).1
    have e2 : beta S.d S.Hm x w = (q : ℂ) ^ n * beta S.d S.Hm x L := by rw [hbL]; field_simp
    rw [e2, map_mul, norm_mul, hqn] at h
    have hp : (0 : ℝ) < (q : ℝ) ^ (-(n : ℤ)) := by positivity
    have : (q : ℝ) ^ (-(2 * n : ℤ)) = (q : ℝ) ^ (-(n : ℤ)) * (q : ℝ) ^ (-(n : ℤ)) := by
      rw [← zpow_add₀ (by positivity)]; ring_nf
    rw [this] at h
    exact le_of_mul_le_mul_left h hp

  set lamV := (N₀ : ℂ) • L with hlamV
  have hlamL : lamV ∈ S.La := by rw [hlamV, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hL _
  have hliftY : liftY q n ((N₀ : ℂ) * e0) b yt = (((N₀ : ℂ) * e0) / (q : ℂ) ^ n) • B := rfl
  have hysplit : ((N₀ : ℂ) / (q : ℂ) ^ n) • v = liftY q n ((N₀ : ℂ) * e0) b yt + lamV := by
    rw [hliftY, hlamV, hLdef, hwdef]
    simp only [smul_sub, smul_smul]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    module
  have hkapt : kap S.Hm lamV t = 1 := by
    obtain ⟨k, hk⟩ := himI L hL _ hNt
    refine kap_eq_one _ _ _ k ?_
    rw [hlamV, hf_smul_left, ← hk, hf_smul_right, hN0r]
  have hWl : opW S.d S.Hm lamV (opU S.Hm t e) = opU S.Hm t e := by
    have h1 := (H1 lamV t e).2.1
    conv_rhs => rw [← he.2 lamV hlamL]
    funext z
    rw [opW, h1, hkapt]
    simp only [opU, opW]
    ring
  have hβ : beta S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) lamV ∈ OK S.d := by
    have hγOK : (N₀ : ℂ) * (N₀ : ℂ) * e0 * beta S.d S.Hm B L ∈ OK S.d :=
      hmulOK _ _ (hmulOK _ _ (hmulOK _ _ (hnatOK _) (hnatOK _)) he0') (hLOK B hB)
    have e3 : beta S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) lamV =
        (N₀ : ℂ) * (N₀ : ℂ) * e0 * beta S.d S.Hm B L / (q : ℂ) ^ n := by
      rw [hliftY, hlamV, bsl, bsr, hN0r]; ring
    rw [e3]
    refine hdiv _ n hγOK ?_ ?_
    · rw [map_mul, norm_mul]
      have h4 : ‖ι ((N₀ : ℂ) * (N₀ : ℂ) * e0)‖ ≤ 1 := by
        rw [map_mul, map_mul, norm_mul, norm_mul]
        exact mul_le_one₀ (mul_le_one₀ (hnat _) (norm_nonneg _) (hnat _)) (norm_nonneg _) (hOK1 _ he0')
      calc _ ≤ 1 * (q : ℝ) ^ (-(n : ℤ)) := mul_le_mul h4 (hLs B hB) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have h5 := hOK1 _ (hconjOK _ (hLOK B hB))
      have h6 := hnat N₀
      simp only [map_mul, hN0r, norm_mul]
      calc _ ≤ 1 * 1 * (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := by gcongr
        _ ≤ _ := by rw [one_mul, one_mul, mul_one]; exact hpow_le
  have hWeq : opW S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (opU S.Hm t e) =
      opW S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) (opU S.Hm t e) := by
    rw [hysplit, ← (H1 _ lamV _).2.2 hβ, hWl]

  have hkap : ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) (((N₀ : ℂ) / (q : ℂ) ^ n) • v) =
      kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n ((N₀ : ℂ) * e0) b yt) := by
    intro a
    set D : Fin g → ℂ := ∑ i, (((a i / q ^ n : ℕ)) : ℂ) • b i with hD
    have hDL : D ∈ S.La := Submodule.sum_mem _ fun i _ => by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
    have hsplitA : ∑ i, (a i : ℂ) • b i = vecA n b (fun i => (a i : ℤ_[q])) + (q : ℂ) ^ n • D := by
      rw [vecA, hD, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_natCast, ZMod.val_natCast, smul_smul, ← add_smul]
      congr 1
      have h : ((a i % q ^ n + q ^ n * (a i / q ^ n) : ℕ) : ℂ) = (a i : ℂ) := by rw [Nat.mod_add_div]
      push_cast at h
      linear_combination -h
    have hkD : kap S.Hm ((q : ℂ) ^ n • D) (liftY q n ((N₀ : ℂ) * e0) b yt) = 1 := by
      obtain ⟨k, hk⟩ := himI D hDL _ (GlobalTheory.MomOne.LiftChange.smul_mem S hS hepsOK hB)
      refine kap_eq_one _ _ _ k ?_
      have : hf S.Hm ((q : ℂ) ^ n • D) (liftY q n ((N₀ : ℂ) * e0) b yt) = hf S.Hm D (((N₀ : ℂ) * e0) • B) := by
        rw [hf_smul_left, hliftY, hf_smul_right, hf_smul_right, map_div₀, hqr]
        field_simp
      rw [this]; exact hk
    have hsumL : ∑ i, (a i : ℂ) • b i ∈ S.La := Submodule.sum_mem _ fun i _ => by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
    have hkl : kap S.Hm (∑ i, (a i : ℂ) • b i) lamV = 1 := by
      obtain ⟨k, hk⟩ := himI _ hsumL lamV hlamL
      exact kap_eq_one _ _ _ k hk
    rw [hysplit, (H6 _ _ _).1, hkl, mul_one, hsplitA, (H6 _ _ _).2, hkD, mul_one]
  exact ⟨hre, 2 * n, (N₀ : ℂ) * e0, yt, hidem, le_rfl, htI, hWeq, hkap⟩

end GlobalTheory.MomN
