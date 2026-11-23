import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

section Frob

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime]

omit [IsUnitBall O K] [Fact l.Prime] in
theorem wS_mul_le_add {s : ℕ} (hl : 2 ≤ l) (hs : s ≤ e) (q : ℕ) :
    wS K e (l * q) ≤ wS K e (q + s) := by
  by_cases h : q + s ≤ l * q
  · exact wS_anti e h
  · push_neg at h
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0
        have : s = 0 := by omega
        subst this
        nlinarith
      · exact h0
    have h1 : (q + s) / e < 2 := by
      rw [Nat.div_lt_iff_lt_mul he]
      nlinarith
    have h2 : ((q + s) / e).factorial = 1 := by
      interval_cases ((q + s) / e) <;> rfl
    have h3 : wS K e (q + s) = 1 := by
      rw [wS, h2, Nat.cast_one, norm_one]
    rw [h3]
    exact wS_le_one e _

theorem exists_frob_eq_X_pow_mul {F : K⟦X⟧} (hF : F ∈ S O K e) {s : ℕ} (hs : s ≤ e)
    (hd : (X : K⟦X⟧) ^ s ∣ F) : ∃ G ∈ S O K e, frob K l F = X ^ (s * l) * G := by
  have hl := (Fact.out : l.Prime).two_le
  refine ⟨PowerSeries.mk fun n => coeff (n + s * l) (frob K l F), ?_, ?_⟩
  · have key : ∀ n, ‖coeff n (PowerSeries.mk fun n => coeff (n + s * l) (frob K l F))‖ * wS K e n ≤
        ‖coeff (n / l + s) F‖ * wS K e (n / l + s) := by
      intro n
      rw [coeff_mk, coeff_frob]
      split_ifs with h
      · have h2 : l ∣ n := (Nat.dvd_add_left (dvd_mul_left l s)).1 h
        have h1 : (n + s * l) / l = n / l + s := Nat.add_mul_div_right _ _ (by omega)
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        obtain ⟨q, rfl⟩ := h2
        rw [Nat.mul_div_cancel_left q (by omega)]
        exact wS_mul_le_add hl hs q
      · rw [norm_zero, zero_mul]
        exact mul_nonneg (norm_nonneg _) (wS_nonneg e _)
    refine ⟨fun n => (key n).trans (hF.1 _), ?_⟩
    have ht : Tendsto (fun n : ℕ => n / l + s) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right _ _) (Nat.tendsto_div_const_atTop (by omega))
    exact squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) key (hF.2.comp ht)
  · ext n
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [coeff_mk, Nat.sub_add_cancel h]
    · rw [coeff_frob]
      split_ifs with h'
      · obtain ⟨G, rfl⟩ := hd
        rw [coeff_X_pow_mul', if_neg]
        intro h''
        have : s * l ≤ n / l * l := Nat.mul_le_mul_right l h''
        have := Nat.div_mul_le_self n l
        omega
      · rfl

end Frob

section Chars

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

theorem mem_uPow_succ_of_inertia {j : ℕ} {w : Vec K a ι} (hw : w ∈ uPow K a ι j)
    (hinv : ∀ ζ, Δ.act (TameGal.inertia ζ) w = w) (hc : ∀ τ, -(j : ZMod e) ∉ Δ.chars τ) :
    w ∈ uPow K a ι (j + 1) := by
  obtain ⟨w', rfl⟩ := mem_uPow_iff_exists.1 hw
  have key : ∀ ζ τ i, C ((TameGal.inertia ζ : TameGal K l e a).root τ) ^ j *
      Δ.act (TameGal.inertia ζ) w' τ i = w' τ i := by
    intro ζ τ i
    have h := Δ.act_smul_tot (TameGal.inertia ζ) ((fun _ => X) ^ j) w'
    rw [map_pow, ringAct_X] at h
    have h2 := congrFun (congrFun
      ((show Δ.act _ ((X : K⟦X⟧) ^ j • w') = _ from h).symm.trans (hinv ζ)) τ) i
    simp only [Pi.smul_apply', Pi.smul_apply, Pi.pow_apply, smul_eq_mul, mul_pow] at h2
    exact mul_left_cancel₀ (pow_ne_zero j X_ne_zero) (by linear_combination h2)
  have hred : ∀ ζ τ, ((TameGal.inertia ζ : TameGal K l e a).root τ) ^ j •
      Δ.actD (TameGal.inertia ζ) (red w') τ = red w' τ := by
    intro ζ τ
    ext i
    have h := congrArg constantCoeff (key ζ τ i)
    rw [map_mul, map_pow, constantCoeff_C] at h
    rw [← Δ.red_act]
    exact h
  have hzero : ∀ τ, red w' τ = 0 := by
    intro τ
    by_contra hne
    refine hc τ ⟨red w', hne, fun ζ => ?_⟩
    have hdvd : e ∣ (-(j : ZMod e)).val + j := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    obtain ⟨k, hk⟩ := hdvd
    rw [← hred ζ τ, smul_smul, ← pow_add, hk, pow_mul, TameGal.root_pow, one_pow, one_smul]
  intro τ i
  have h0 : constantCoeff (w' τ i) = 0 := congrFun (hzero τ) i
  change (X : K⟦X⟧) ^ (j + 1) ∣ X ^ j * w' τ i
  rw [pow_succ]
  exact mul_dvd_mul_left _ (X_dvd_iff.2 h0)

end Descent

omit [NeZero e] in

theorem le_mul_pow_of_frobPeriod_le {j r b : ℕ} (hb : 0 < b) (hlb : (l : ZMod e) ^ b = 1) (hj : 0 < j)
    (hc : frobPeriod l (-(j : ZMod e)) ≤ r) : e ≤ j * l ^ r := by
  have hl := (Fact.out : l.Prime).two_le
  set c : ZMod e := -(j : ZMod e)
  have hper : Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) b c := by
    change (fun x : ZMod e => (l : ZMod e) * x)^[b] c = c
    rw [mul_left_iterate]
    simp [hlb]
  have hpos : 0 < frobPeriod l c := hper.minimalPeriod_pos hb
  have hfix := Function.isPeriodicPt_minimalPeriod (fun x : ZMod e => (l : ZMod e) * x) c
  set ρ := frobPeriod l c with hρ
  have hfix' : (l : ZMod e) ^ ρ * c = c := by
    have := hfix.eq
    rw [mul_left_iterate] at this
    exact this
  have hlρ : 2 ≤ l ^ ρ := le_trans hl (Nat.le_self_pow (by omega) l)
  have hdvd : e ∣ (l ^ ρ - 1) * j := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub (by omega : 1 ≤ l ^ ρ)]
    have : ((l : ZMod e) ^ ρ - 1) * c = 0 := by rw [sub_mul, hfix', one_mul, sub_self]
    simp only [c] at this
    linear_combination -this
  have h1 := Nat.le_of_dvd (Nat.mul_pos (by omega) hj) hdvd
  calc e ≤ (l ^ ρ - 1) * j := h1
    _ ≤ l ^ ρ * j := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ l ^ r * j := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hc)
    _ = j * l ^ r := mul_comm _ _

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

theorem exists_mem_uPow_of_inertia (r : ℕ) (hr : ∀ τ, ∀ c ∈ Δ.chars τ, frobPeriod l c ≤ r)
    {w : Vec K a ι} (hw : w ∈ uPow K a ι 1) (hinv : ∀ ζ, Δ.act (TameGal.inertia ζ) w = w) :
    ∃ s, s ≤ e ∧ e ≤ s * l ^ r ∧ w ∈ uPow K a ι s := by
  have he := NeZero.pos e
  have hl := (Fact.out : l.Prime).two_le
  suffices H : ∀ k j, e - j = k → 1 ≤ j → j ≤ e → w ∈ uPow K a ι j →
      ∃ s, s ≤ e ∧ e ≤ s * l ^ r ∧ w ∈ uPow K a ι s from H _ 1 rfl le_rfl he hw
  intro k
  induction k with
  | zero =>
    intro j hk hj hje hwj
    refine ⟨j, hje, ?_, hwj⟩
    have : j = e := by omega
    subst this
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) r)
  | succ k ih =>
    intro j hk hj hje hwj
    by_cases h : ∃ τ, -(j : ZMod e) ∈ Δ.chars τ
    · obtain ⟨τ, hτ⟩ := h
      have hla : (l : ZMod e) ^ a = 1 := by
        have h := congrArg (fun n : ℕ => (n : ZMod e)) (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a))
        simp only [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one, Nat.cast_pow] at h
        exact h.symm
      exact ⟨j, hje, le_mul_pow_of_frobPeriod_le (NeZero.pos a) hla (by omega) (hr τ _ hτ), hwj⟩
    · push_neg at h
      exact ih (j + 1) (by omega) (by omega) (by omega) (Δ.mem_uPow_succ_of_inertia hwj hinv h)

end Descent

end Chars

section Series

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem mul_le_pow_of_two_le_base {l : ℕ} (hl : 2 ≤ l) (t : ℕ) : t * l ≤ l ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have h1 : l ≤ l ^ t := Nat.le_self_pow (by omega) l
      calc (t + 1) * l = t * l + l := by ring
        _ ≤ l ^ t + l ^ t := by omega
        _ ≤ l ^ t * l := by nlinarith
        _ = l ^ (t + 1) := (pow_succ _ _).symm

omit [IsUltrametricDist K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem C_smul_vec (c : K) (v : Vec K a ι) : (C c : K⟦X⟧) • v = c • v := by
  ext τ i
  simp only [Pi.smul_apply, smul_eq_mul, smul_eq_C_mul]

namespace PhiMod

variable (P : PhiMod O K l e a ι)

theorem mem_MM_of_l_approx {w : Vec K a ι} (h : ∀ k : ℕ, ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
    w - (s + (l : K) ^ k • g) ∈ uPow K a ι m) : w ∈ P.MM := by
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h k
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

theorem lphi_pow_eq_smul_phi_pow (n : ℕ) (v : Vec K a ι) :
    (P.lphi ^ n) v = (l : K) ^ n • (P.phi ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ' P.phi, Module.End.mul_apply, lphi_apply,
      map_smul, smul_smul, ← pow_succ']

theorem phi_pow_X_pow_smul_eq (n k : ℕ) (v : Vec K a ι) :
    (P.phi ^ n) ((X : K⟦X⟧) ^ k • v) = (X : K⟦X⟧) ^ (k * l ^ n) • (P.phi ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, phi_smul, map_pow, frob_X, ← pow_mul,
      Module.End.mul_apply]
    congr 2
    ring

omit [NormedAlgebra ℚ_[l] K] in
theorem l_pow_smul_phi_pow_mem_MM {η : ℕ} (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM)
    (n : ℕ) {v : Vec K a ι} (hv : v ∈ P.MM) : (l : K) ^ (n * η) • (P.phi ^ n) v ∈ P.MM := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have := hη _ ih
    rw [map_smul, smul_smul, ← pow_add] at this
    rw [pow_succ', Module.End.mul_apply, show (n + 1) * η = η + n * η by ring]
    exact this

variable [NeZero e]

theorem exists_phi_eq_X_pow_smul_of_mem_uPow {η : ℕ}
    (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM) {s : ℕ} (hs : s ≤ e) {w : Vec K a ι}
    (hw : w ∈ P.MM) (hws : w ∈ uPow K a ι s) :
    ∃ x, (l : K) ^ η • x ∈ P.MM ∧ P.phi w = (X : K⟦X⟧) ^ (s * l) • x := by
  have hF : ∀ i τ, (P.mxInv τ *ᵥ w τ) i ∈ S O K e := fun i τ => P.mem_extc_iff.1 (mem_tot.1 hw τ) i
  have hd : ∀ i τ, (X : K⟦X⟧) ^ s ∣ (P.mxInv τ *ᵥ w τ) i := fun i τ => dvd_mulVec _ (hws τ) i
  choose G hG hGe using fun i τ => exists_frob_eq_X_pow_mul (l := l) (hF i τ) hs (hd i τ)
  refine ⟨∑ i, (fun τ => G i (τ - 1)) • P.phi (P.phi (bas i)), ?_, ?_⟩
  · rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    exact P.smul_tot_mem_ext (fun τ => hG i _)
      (hη _ (P.ext_mono (A_le_S l e) (P.phi_mem_L (P.bas_mem_M i))))
  · conv_lhs => rw [P.eq_sum_phi_bas w]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [phi_smul_tot]
    ext τ j
    simp only [Pi.smul_apply', Pi.smul_apply, frobTot_apply, hGe, smul_eq_mul, mul_assoc]

end PhiMod

end Series

theorem l_pow_smul_zeta_phi_mem_MM : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) →
    (r + 2) * η < l + 1 → l ≠ 2 → ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.zeta (D.phi m) ∈ D.MM := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D r hr1 hr hηl _ m hm
  have hl := (Fact.out : l.Prime).two_le
  have hηle : η ≤ l := by nlinarith
  have hη : ∀ v ∈ D.MM, (l : K) ^ η • D.phi v ∈ D.MM :=
    PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper
  set w := D.conn (D.phi m) with hwdef
  have hwMM : w ∈ D.MM := D.conn_mem_MM (D.ext_mono (A_le_S l e) (D.phi_mem_L hm.1))
  have hw1 : w ∈ uPow K a ι 1 := D.conn_mem_uPow _
  have hinv : ∀ ζ, D.desc.act (TameGal.inertia ζ) w = w := fun ζ => by
    rw [hwdef, Descent.act_conn, Descent.act_phi, hm.2]
  obtain ⟨s, hse, hes, hws⟩ := D.desc.exists_mem_uPow_of_inertia r hr hw1 hinv
  obtain ⟨x, hx, hφw⟩ := D.exists_phi_eq_X_pow_smul_of_mem_uPow hη hse hwMM hws
  have hterm : ∀ n, (D.lphi ^ (n + 1)) w =
      (l : K) ^ (n + 1) • (X : K⟦X⟧) ^ (s * l ^ (n + 1)) • (D.phi ^ n) x := by
    intro n
    rw [PhiMod.lphi_pow_eq_smul_phi_pow, pow_succ D.phi n, Module.End.mul_apply, hφw,
      PhiMod.phi_pow_X_pow_smul_eq]
    congr 3
    ring
  have hy : ∀ n, (l : K) ^ ((n + 1) * η) • (D.phi ^ n) x ∈ D.MM := fun n => by
    have := D.l_pow_smul_phi_pow_mem_MM hη n hx
    rw [map_smul, smul_smul, ← pow_add] at this
    rwa [show (n + 1) * η = n * η + η by ring]
  have hcancel : ∀ (T z : Vec K a ι) (A B t : ℕ), z ∈ D.MM → B + t ≤ A →
      (l : K) ^ B • T = (l : K) ^ A • z → ∃ g ∈ D.MM, T = (l : K) ^ t • g := by
    intro T z A B t hz hBA h
    refine ⟨(l : K) ^ (A - B - t) • z, D.l_pow_smul_mem_MM _ hz, ?_⟩
    apply smul_right_injective _ (pow_ne_zero B (l_ne_zero (K := K) l))
    simp only
    rw [h, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  have hT : ∀ n, ∃ g ∈ D.MM, (l : K) ^ (η * (r + 1)) • (D.lphi ^ (n + 1)) w = (l : K) ^ (n - r) • g := by
    intro n
    rw [hterm]
    by_cases hn : n ≤ r
    · refine hcancel _ ((X : K⟦X⟧) ^ (s * l ^ (n + 1)) • ((l : K) ^ ((n + 1) * η) • (D.phi ^ n) x))
        (η * (r + 1) + (n + 1)) ((n + 1) * η) (n - r) (D.smul_mem_MM (pow_mem HasU.X_mem _) (hy n)) ?_ ?_
      · have : n - r = 0 := by omega
        rw [this]
        nlinarith
      · rw [smul_comm ((X : K⟦X⟧) ^ _) ((l : K) ^ _), smul_smul, smul_smul, smul_smul, ← pow_add,
          ← pow_add, ← pow_add]
        congr 2
        ring
    · push_neg at hn
      obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
      have hle : e * l ^ (t + 1) ≤ s * l ^ (r + t + 1) :=
        calc e * l ^ (t + 1) ≤ s * l ^ r * l ^ (t + 1) := Nat.mul_le_mul_right _ hes
          _ = s * l ^ (r + t + 1) := by ring
      have hl0 : (l : K) ≠ 0 := l_ne_zero l
      have hμ : monomial (e * l ^ (t + 1)) (((l : K) ^ (l ^ t))⁻¹) ∈ S O K e := by
        refine monomial_mem_S ?_
        rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv, norm_pow,
          inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _)]
        refine (norm_factorial_le l _).trans ?_
        rw [show l ^ (t + 1) / l = l ^ t by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]]
      have hX : (X : K⟦X⟧) ^ (s * l ^ (r + t + 1)) = C ((l : K) ^ (l ^ t)) *
          (X ^ (s * l ^ (r + t + 1) - e * l ^ (t + 1)) * monomial (e * l ^ (t + 1)) ((l : K) ^ (l ^ t))⁻¹) := by
        have hc : C ((l : K) ^ (l ^ t)) * C (((l : K) ^ (l ^ t))⁻¹) = 1 := by
          rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
        rw [monomial_eq_C_mul_X_pow]
        calc (X : K⟦X⟧) ^ (s * l ^ (r + t + 1)) =
            X ^ (s * l ^ (r + t + 1) - e * l ^ (t + 1)) * X ^ (e * l ^ (t + 1)) := by
              rw [← pow_add, Nat.sub_add_cancel hle]
          _ = _ := by linear_combination (X ^ (s * l ^ (r + t + 1) - e * l ^ (t + 1)) * (X : K⟦X⟧) ^ (e * l ^ (t + 1))) * hc.symm
      refine hcancel _ ((X ^ (s * l ^ (r + t + 1) - e * l ^ (t + 1)) *
          monomial (e * l ^ (t + 1)) ((l : K) ^ (l ^ t))⁻¹) • ((l : K) ^ ((r + t + 1) * η) • (D.phi ^ (r + t)) x))
        (η * (r + 1) + (r + t + 1) + l ^ t) ((r + t + 1) * η) (r + t - r)
        (D.smul_mem_MM (mul_mem (pow_mem HasU.X_mem _) hμ) (hy _)) ?_ ?_
      · have h1 := mul_le_pow_of_two_le_base hl t
        have h2 : t * η ≤ t * l := Nat.mul_le_mul_left t hηle
        rw [Nat.add_sub_cancel_left]
        nlinarith
      · rw [show r + t + 1 = r + t + 1 from rfl, hX, mul_smul, C_smul_vec,
          smul_comm (_ : K⟦X⟧) ((l : K) ^ ((r + t + 1) * η))]
        simp only [smul_smul, ← pow_add]
        congr 2
        ring
  choose g hg hgeq using hT
  apply D.mem_MM_of_l_approx
  intro k
  refine ⟨-∑ n ∈ Finset.range (k + r), (l : K) ^ (n - r) • g n,
    neg_mem (Submodule.sum_mem _ fun n _ => D.l_pow_smul_mem_MM _ (hg n)), fun mm => ?_⟩
  refine ⟨-∑ n ∈ Finset.Ico (k + r) (k + r + mm), (l : K) ^ (n - r - k) • g n,
    neg_mem (Submodule.sum_mem _ fun n _ => D.l_pow_smul_mem_MM _ (hg n)), ?_⟩
  have hsplit : (l : K) ^ k • (-∑ n ∈ Finset.Ico (k + r) (k + r + mm), (l : K) ^ (n - r - k) • g n) =
      -∑ n ∈ Finset.Ico (k + r) (k + r + mm), (l : K) ^ (n - r) • g n := by
    rw [smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [smul_smul, ← pow_add]
    have := (Finset.mem_Ico.1 hn).1
    congr 2
    omega
  rw [hsplit, ← neg_add, Finset.sum_range_add_sum_Ico _ (by omega : k + r ≤ k + r + mm), sub_neg_eq_add]
  have hsum : ∑ n ∈ Finset.range (k + r + mm), (l : K) ^ (n - r) • g n =
      (l : K) ^ (η * (r + 1)) • ∑ n ∈ Finset.range (k + r + mm), (D.lphi ^ (n + 1)) w := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun n _ => (hgeq n).symm
  rw [hsum, ← smul_add]
  have h := (uPow K a ι _).smul_mem (C ((l : K) ^ (η * (r + 1)))) (D.zeta_add_sum_mem (D.phi m) (k + r + mm))
  rw [C_smul_vec] at h
  exact uPow_anti (by omega) h

end GlobalTheory.BK
