import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan

noncomputable section

open TensorProduct MvPolynomial
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

namespace Formalism.CohomologicalDescent.E

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

def ThinAE : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).ThinA P

def ThickAE : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).ThickA P

def CloudAE : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (W : Wts ι), W.Ok P → ∀ J : ℕ → ℕ,
    (W.sizeData₂ P J).CloudA P

def BeyondHE : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι),
    W.Ok P → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) → P.h < (l : ℝ) →
    (∀ τ, W.ex P τ l = 0) ∧ W.JA P l = 0 ∧ W.JW P l = 0

def RecIncl7E : Prop :=
  ExIntervalLt → ExCut → LemmaDGraded → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    ∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Jmin l ≤ W.Jrec7 P l

def InputsRec7E : Prop :=
  ExIntervalLt → ExCut → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → (W.sizeData₂ P (W.Jrec7 P)).Inputs P

def RecSum7E : Prop :=
  ExIntervalLt → ExCut → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
        totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)

def CorollaryExceptionalStrict : Prop :=
  ExIntervalLt → ExCut → LemmaDGraded → PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2) ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          totalBound P W.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)

def Tail7E : Prop :=
  ExIntervalLt → ExCut → PrimeCountingBound → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → LargeParameterEstimates.Rows P X' A → LargeParameterEstimates.Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b

def Ev7E : Prop :=
  ExIntervalLt → ExCut → PrimeCountingBound → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    LargeParameterEstimates.Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l) ∧ (X l).Incl l ((X l).Jmin l) ∧
      (X l).Jmin l ≤ W.Jrec7 P l) ∧
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ∧
      ∑ l ∈ Q, ((X l).Jmin l : ℝ) * Real.log (l : ℝ) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b

theorem res_anti_shift {N a : ℕ} {lam : ℕ → ℕ} (h : Antitone (res N lam)) :
    Antitone (res (N - a) (fun i => lam (a + i))) := by
  intro i j hij
  have hi : a + i.val < N := by have := i.isLt; omega
  have hj : a + j.val < N := by have := j.isLt; omega
  have hle : (⟨a + i.val, hi⟩ : Fin N) ≤ ⟨a + j.val, hj⟩ := by
    rw [Fin.mk_le_mk]
    have := Fin.le_iff_val_le_val.mp hij
    omega
  exact h hle

theorem exZ_rank_le_one {N : ℕ} (hN : N ≤ 1) (ν : Fin N → ℕ) (l : ℕ) (hl : l.Prime) :
    LA.exZ N N le_rfl ν l = 0 := by
  have hanti : Antitone ν := by
    intro i j _
    have hi := i.isLt
    have hj := j.isLt
    have : i = j := Fin.ext (by omega)
    rw [this]
  have h := LA.lattice_z_rank_le_two N N le_rfl (by omega) ν hanti l hl
  have he : Formalism.RankGapBounds.JumpSetsAlt.eExp (LA.lamU N N ν) l = 0 := by
    unfold Formalism.RankGapBounds.JumpSetsAlt.eExp
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Formalism.RankGapBounds.JumpSetsAlt.posPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    have h3 : p.1.val < p.2.val := hp
    omega
  rw [he] at h
  exact Nat.le_zero.mp (Nat.sInf_le h)

theorem exZ_le_of_exCut (hC : ExCut) (l : ℕ) (hl : l.Prime) (w : ℕ) :
    ∀ (N : ℕ) (lam : ℕ → ℕ), Antitone (res N lam) → ∀ lo : ℤ,
      (∀ a < N, lo ≤ UN N lam a ∧ UN N lam a ≤ lo + (w : ℤ)) →
      LA.exZ N N le_rfl (res N lam) l ≤ N.choose 2 * Nat.log l w := by
  intro N
  induction N with
  | zero =>
    intro lam _ lo _
    rw [exZ_rank_le_one (by norm_num) (res 0 lam) l hl]
    exact Nat.zero_le _
  | succ n ih =>
    intro lam hA lo hb

    have hcut : LA.exZ (n + 1) (n + 1) le_rfl (res (n + 1) lam) l ≤
        LA.exZ 1 1 le_rfl (res 1 lam) l +
          LA.exZ n n le_rfl (res n (fun i => lam (1 + i))) l + 1 * n * Nat.log l w :=
      hC (n + 1) lam hA l hl lo w hb 1 (by omega)
    have h1 : LA.exZ 1 1 le_rfl (res 1 lam) l = 0 := exZ_rank_le_one le_rfl _ l hl
    have hA' : Antitone (res n (fun i => lam (1 + i))) := res_anti_shift (a := 1) hA
    have hb' : ∀ a < n, lo ≤ UN n (fun i => lam (1 + i)) a ∧
        UN n (fun i => lam (1 + i)) a ≤ lo + (w : ℤ) := by
      intro a ha
      have hba := hb (1 + a) (by omega)
      have e : UN n (fun i => lam (1 + i)) a = UN (n + 1) lam (1 + a) := by
        simp only [UN]
        push_cast
        ring
      rw [e]
      exact hba
    have hrest := ih (fun i => lam (1 + i)) hA' lo hb'
    have hch : (n + 1).choose 2 = n.choose 2 + n := by
      have h2 := Nat.choose_succ_succ n 1
      rw [Nat.choose_one_right] at h2
      exact h2.trans (Nat.add_comm _ _)
    rw [h1] at hcut
    rw [hch, Nat.add_mul]
    have hstep : 0 + LA.exZ n n le_rfl (res n (fun i => lam (1 + i))) l + 1 * n * Nat.log l w ≤
        n.choose 2 * Nat.log l w + n * Nat.log l w := by
      rw [zero_add, one_mul]
      exact Nat.add_le_add_right hrest _
    exact le_trans hcut hstep

theorem exIntervalLt_of_exCut : ExCut → ExIntervalLt := by
  intro hC N lam hA l hl lo w hb
  have h := exZ_le_of_exCut hC l hl w N lam hA lo hb
  refine ⟨h, fun hw => ?_⟩
  have h0 : Nat.log l w = 0 := Nat.log_of_lt hw
  rw [h0, mul_zero] at h
  exact Nat.le_zero.mp h

theorem thin_exceptional : ThinAE := by
  intro hI _ P hH hL ι W hW J τ _ l hl
  have hN := rank_pos_of_hyp P hH
  have h := hI P.Nr (W.lam τ) (restriction_lambda_antitone hW τ) l hl (W.U P τ (P.Nr - 1))
    (W.width P τ).toNat (fun a ha => weight_in_width_range hW τ a ha)
  have hc : (((W.width P τ).toNat : ℕ) : ℝ) = (W.width P τ : ℝ) := by
    have : (((W.width P τ).toNat : ℕ) : ℤ) = W.width P τ := Int.toNat_of_nonneg (width_nonneg hW hN τ)
    exact_mod_cast this
  constructor
  · intro hlt
    apply h.2
    have h1 : (((W.width P τ).toNat : ℕ) : ℝ) < (l : ℝ) := by rw [hc]; exact hlt
    exact_mod_cast h1
  · intro hle
    have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    have hle' : (l : ℝ) ≤ (W.width P τ : ℝ) := hle
    exact exponent_mul_log_le_choose_mul_log P.Nr l _ _ _ h.1 hc.le (by linarith)

theorem one_le_k_of_hyp (P : Par) (hH : P.Hyp) : 1 ≤ P.k := hH.m_pos.trans hH.m_le

theorem kc_cast_le_k (P : Par) : (kc P : ℝ) ≤ (P.k : ℝ) := by
  unfold kc
  exact_mod_cast Nat.sub_le P.k 1

theorem thick_exceptional : ThickAE := by
  intro hI hC P hH hL ι W hW J τ hτ l hl
  obtain ⟨sh, hS0, hE0⟩ := shape_a_real_holds P hH hL ι W hW τ hτ
  have hh := one_le_h P hH
  have hh0 := floor_height_le_height P hH
  have h := hI P.Nr (W.lam τ) (restriction_lambda_antitone hW τ) l hl 0 (h0 P)
    (fun a ha => by
      have h1 := sh.inRange ⟨a, ha⟩
      rw [zero_add]
      exact h1)
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    apply h.2
    have h1 : (h0 P : ℝ) < (l : ℝ) := lt_of_le_of_lt hh0 hlt
    exact_mod_cast h1
  · exact exponent_mul_log_le_choose_mul_log P.Nr l _ _ _ h.1 hh0 hh
  · intro hle
    have heta : (W.U P τ (kc P) - W.U P τ (P.Nr - 1)).toNat < l := by
      have ht1 : (1 : ℝ) ≤ (P.t : ℝ) := by
        have := hH.t_ge
        exact_mod_cast (show 1 ≤ P.t by omega)
      have h1 : (((W.U P τ (kc P) - W.U P τ (P.Nr - 1)).toNat : ℕ) : ℝ) < (l : ℝ) := by
        linarith
      exact_mod_cast h1
    have hjq := (rest_near_holds P hH ι W hW τ).2.2.2.1
    have hrows := hW.what₂ τ
    have hNk : P.Nr - kc P ≤ P.m + P.t := by omega
    have hs := SL2BinomialLattices.size_large l P.Nr (kc P) (h0 P) _ _ 0 P.m P.t _ _ _ hl sh (Nat.zero_le _) heta.le hNk
    have hkN : kc P ≤ P.Nr := sh.k_le
    have hcut := hC P.Nr (W.lam τ) (restriction_lambda_antitone hW τ) l hl 0 (h0 P)
      (fun a ha => by
        have h1 := sh.inRange ⟨a, ha⟩
        rw [zero_add]
        exact h1) (kc P) hkN
    have hcl := (hI (kc P) (W.lam τ) (restriction_lambda_antitone_kc hW τ) l hl
      (W.xm τ - ((P.Nr : ℤ) - (kc P : ℤ))) (W.xp τ - W.xm τ).toNat (fun a ha => by
        have h1 := hW.cloud τ a ha
        have h2 := (hW.window τ).2.1
        unfold Wts.U UN at h1
        unfold UN
        omega)).1
    have hrest := (hI (P.Nr - kc P) (fun i => W.lam τ (kc P + i)) (res_anti_shift (restriction_lambda_antitone hW τ)) l hl
      (W.U P τ (P.Nr - 1)) (W.U P τ (kc P) - W.U P τ (P.Nr - 1)).toNat (fun a ha => by
        have h1 := sh.restIn ⟨kc P + a, by omega⟩ (by simp)
        simp only at h1
        unfold Wts.U UN at h1 ⊢
        push_cast at h1 ⊢
        omega)).2 heta
    have hexN : W.ex P τ l ≤ (kc P).choose 2 * Nat.log l (W.xp τ - W.xm τ).toNat +
        kc P * (P.Nr - kc P) * Nat.log l (h0 P) := by
      have e0 : W.ex P τ l = LA.exZ P.Nr P.Nr le_rfl (res P.Nr (W.lam τ)) l := rfl
      rw [e0]
      rw [hrest, add_zero] at hcut
      exact hcut.trans (Nat.add_le_add_right hcl _)
    have hexR : (W.ex P τ l : ℝ) ≤ ((kc P).choose 2 : ℝ) * (Nat.log l (W.xp τ - W.xm τ).toNat : ℝ) +
        (kc P : ℝ) * ((P.Nr - kc P : ℕ) : ℝ) * (Nat.log l (h0 P) : ℝ) := by
      exact_mod_cast hexN
    have hlg0 : (0 : ℝ) ≤ Real.log (l : ℝ) := Real.log_natCast_nonneg l
    have g1 := SL2BinomialLattices.log_le_log_bound l (W.xp τ - W.xm τ).toNat
    have g2 := SL2BinomialLattices.log_le_log_bound l (h0 P)
    have hmain : (W.ex P τ l : ℝ) * Real.log l ≤
        (kc P : ℝ) * ((P.Nr - kc P : ℕ) : ℝ) * Real.log (h0 P : ℕ) +
          ((kc P).choose 2 : ℝ) * Real.log ((W.xp τ - W.xm τ).toNat : ℕ) := by
      calc (W.ex P τ l : ℝ) * Real.log l
          ≤ (((kc P).choose 2 : ℝ) * (Nat.log l (W.xp τ - W.xm τ).toNat : ℝ) +
              (kc P : ℝ) * ((P.Nr - kc P : ℕ) : ℝ) * (Nat.log l (h0 P) : ℝ)) * Real.log l :=
            mul_le_mul_of_nonneg_right hexR hlg0
        _ = ((kc P).choose 2 : ℝ) * ((Nat.log l (W.xp τ - W.xm τ).toNat : ℝ) * Real.log l) +
              (kc P : ℝ) * ((P.Nr - kc P : ℕ) : ℝ) * ((Nat.log l (h0 P) : ℝ) * Real.log l) := by ring
        _ ≤ ((kc P).choose 2 : ℝ) * Real.log ((W.xp τ - W.xm τ).toNat : ℕ) +
              (kc P : ℝ) * ((P.Nr - kc P : ℕ) : ℝ) * Real.log (h0 P : ℕ) :=
            add_le_add (mul_le_mul_of_nonneg_left g1 (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left g2 (by positivity))
        _ = _ := by ring
    refine (hmain.trans hs.2).trans ?_
    have hk := kc_cast_le_k P
    have hk0 : (0 : ℝ) ≤ (kc P : ℝ) := Nat.cast_nonneg _
    have h01 : (1 : ℝ) ≤ (h0 P : ℝ) := by exact_mod_cast one_le_floor_height P hH
    have hl1 : 0 ≤ Real.log (3 * (h0 P : ℝ)) := Real.log_nonneg (by linarith)
    have hl2 : Real.log (3 * (h0 P : ℝ)) ≤ Real.log (3 * P.h) :=
      Real.log_le_log (by linarith) (by linarith)
    have hmt : (0 : ℝ) ≤ (P.m : ℝ) + (P.t : ℝ) := by positivity
    have t1 : (kc P : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * (h0 P : ℝ)) ≤
        (P.k : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * P.h) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hk hmt) hl2 hl1
        (mul_nonneg (Nat.cast_nonneg _) hmt)
    have hk1 : (1 : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast one_le_k_of_hyp P hH
    have hSk : 0 ≤ Real.log (P.S + (P.k : ℝ)) := Real.log_nonneg (by linarith [hH.S_nonneg])
    have t2 : (kc P : ℝ) ^ 2 * Real.log ((((W.xp τ - W.xm τ).toNat : ℕ) : ℝ) + (kc P : ℝ)) ≤
        (P.k : ℝ) ^ 2 * Real.log (P.S + (P.k : ℝ)) := by
      rcases Nat.eq_zero_or_pos (kc P) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        positivity
      · have hc1 : (1 : ℝ) ≤ (kc P : ℝ) := by exact_mod_cast h0
        have hs0 : (0 : ℝ) ≤ (((W.xp τ - W.xm τ).toNat : ℕ) : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul (pow_le_pow_left₀ hk0 hk 2)
          (Real.log_le_log (by linarith) (by linarith)) (Real.log_nonneg (by linarith)) (by positivity)
    linarith

theorem cloud_exceptional : CloudAE := by
  intro hI _ P hH hL ι W hW J τ hτ l hl hlt
  have hkN := kc_le_rank hW τ
  have h := hI (kc P) (W.lam τ) (restriction_lambda_antitone_kc hW τ) l hl
    (W.xm τ - ((P.Nr : ℤ) - (kc P : ℤ))) (W.xp τ - W.xm τ).toNat (fun a ha => by
      have h1 := hW.cloud τ a ha
      have h2 := (hW.window τ).2.1
      unfold Wts.U UN at h1
      unfold UN
      omega)
  apply h.2
  have hw := hW.window τ
  have h3 : (((W.xp τ - W.xm τ).toNat : ℕ) : ℝ) = (W.xp τ : ℝ) - (W.xm τ : ℝ) := by
    have : (((W.xp τ - W.xm τ).toNat : ℕ) : ℤ) = W.xp τ - W.xm τ :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hw.2.1)
    exact_mod_cast this
  have h4 : (((W.xp τ - W.xm τ).toNat : ℕ) : ℝ) < (l : ℝ) := by
    rw [h3]
    have : (0 : ℝ) ≤ (P.k : ℝ) := Nat.cast_nonneg _
    linarith [hw.1, hw.2.2]
  exact_mod_cast h4

theorem beyond_height_exceptional : BeyondHE := by
  intro hI hC P hH hL ι _ _ W hW l hl hlJ hlh
  have hex : ∀ τ, W.ex P τ l = 0 := by
    intro τ
    by_cases hτ : τ ∈ W.T2
    · exact (thick_exceptional hI hC P hH hL ι W hW (fun _ => 0) τ hτ l hl).1 hlh
    · apply (thin_exceptional hI hC P hH hL ι W hW (fun _ => 0) τ hτ l hl).1
      show (W.width P τ : ℝ) < (l : ℝ)
      have he := paramsTop_holds P hH hL
      have hf := (paramsThin_holds P hH hL).2
      have ht := hL.top_le
      have hb := hH.b'_pos
      have hx : 0 < P.x := by linarith [hH.x_ge]
      have hpos : 0 ≤ P.b' * (1 / P.x + 1 / P.x ^ 2) := by positivity
      rcases hW.other τ hτ with h | h
      · linarith [h.2]
      · nlinarith [h.2]
  refine ⟨hex, ?_, ?_⟩
  · unfold Wts.JA
    exact Finset.sum_eq_zero fun τ _ => hex τ
  · unfold Wts.JW
    apply Finset.sum_eq_zero
    intro τ _
    unfold cTau
    split_ifs
    · simp [hex τ]
    · exact hex τ

theorem recursion_inputs_exceptional : InputsRec7E := by
  intro hI hC P hH hL ι _ _ W hW hcard hSp
  refine ⟨hcard, hSp, ?_, sizeData_boundW_of_le_seventh_recursion W P hH hL hW _ (fun _ _ => le_rfl),
    thin_exceptional hI hC P hH hL ι W hW _, thick_exceptional hI hC P hH hL ι W hW _,
    cloud_exceptional hI hC P hH hL ι W hW _, shape_t_real_holds P hH hL ι W hW _,
    widths_real_holds P ι W hW _⟩
  intro l _ hc
  exact (seventh_recursion_eq_a_of_small_prime W P l hc).le

theorem recursion_sum_exceptional : RecSum7E := by
  intro hI hC hRS P hH hL ι _ _ W hW hcard hSp Q hQ
  exact totalElementary_holds hRS P hH hL ι (W.sizeData₂ P (W.Jrec7 P))
    (recursion_inputs_exceptional hI hC P hH hL ι W hW hcard hSp) (places_real_holds P hH hL ι W hW _).2 Q hQ

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.ThinAReal = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ ThinAE = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.ThickAReal = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ ThickAE = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.CloudAReal = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ CloudAE = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.BeyondH = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ BeyondHE = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.RecIncl7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ RecIncl7E = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.InputsRec7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ InputsRec7E = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.RecSum7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ RecSum7E = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.ShortWeightBounds.CorollaryOfRecord7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ CorollaryExceptionalStrict = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.LargeParameterEstimates.CorollaryOfRecord7Tail = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ Tail7E = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.LargeParameterEstimates.CorollaryOfRecord7Ev = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧ Ev7E = (ExIntervalLt → ExCut → B) :=
  ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.Top.CorollaryOfRecord7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧
    CorollaryOfRecord7E = (ExInterval → ExCut → B) := ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.JD.JointRecord = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧
    JointRecordE = (ExInterval → ExCut → B) := ⟨_, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.Top.CorollaryOfRecord7 = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧
    CorollaryOfRecord7ELt = (ExIntervalLt → ExCut → B) ∧ CorollaryOfRecord7C = (ExCut → B) := ⟨_, rfl, rfl, rfl⟩

example : ∃ B : Prop, Formalism.CohomologicalDescent.JD.JointRecord = (Formalism.CohomologicalDescent.LA.LemmaAZ → B) ∧
    JointRecordELt = (ExIntervalLt → ExCut → B) ∧ JointRecordC = (ExCut → B) := ⟨_, rfl, rfl, rfl⟩

end Formalism.CohomologicalDescent.E
