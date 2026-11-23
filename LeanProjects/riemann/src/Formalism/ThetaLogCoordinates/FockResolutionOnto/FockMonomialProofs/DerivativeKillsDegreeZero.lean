import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.LatDefs
import Formalism.ThetaLogCoordinates.FockResolutionOnto.MulEarlyModP
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Vanish
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

def dEarly {K : ℕ} (LL : Letters (K + 1)) : ℤ := ∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ)

theorem dEarly_nonneg {K : ℕ} (LL : Letters (K + 1)) : 0 ≤ dEarly LL := by
  unfold dEarly
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

theorem dEarly_le_total {K : ℕ} (LL : Letters (K + 1)) : dEarly LL ≤ (LL.total : ℤ) := by
  unfold dEarly Letters.total
  push_cast
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp

section LatW
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}

theorem EX_zero_zero (LL : Letters (K + 1)) (c : ℤ) :
    EX p LL c (0 : Fin (s + 1)) 0 = (((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K (s + 1)) := rfl

theorem EX_zero_succ (LL : Letters (K + 1)) (c : ℤ) (j : Fin s) :
    EX p LL c (0 : Fin (s + 1)) j.succ = dW p K (Fin.castSucc j) := rfl

theorem EX_succ_zero (LL : Letters (K + 1)) (c : ℤ) (i : Fin s) :
    EX p LL c i.succ (0 : Fin (s + 1)) = Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i) := rfl

theorem EX_succ_succ (LL : Letters (K + 1)) (c : ℤ) (i j : Fin s) :
    EX p LL c i.succ j.succ = glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) := rfl

theorem tp_exists (LL : Letters (K + 1)) (hs : 1 ≤ s) (Mt : WithTop ℤ) :
    ∃ P, IsTypeProj p LL (K + 1) (univ.erase (Fin.last s)) {la : Fin (s + 1) → ℤ | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} P := by
  have h0 := zero_mem_erase (Fin.last s) (by omega) (by simp)
  obtain ⟨P, hP, -, -⟩ := (Formalism.InvariantFactorPaths.PW.Top.dischargeP p (K + 1) (s + 1) LL (Fin.last s) _ le_rfl).1 (K + 1) le_rfl
    (univ.erase (Fin.last s)) (Or.inr rfl) {la | ((la 0 : ℤ) : WithTop ℤ) ≤ Mt} (fun la la' hl => by
      show (((la 0 : ℤ) : WithTop ℤ) ≤ Mt) ↔ (((la' 0 : ℤ) : WithTop ℤ) ≤ Mt)
      rw [hl 0 h0])
  exact ⟨P, hP⟩

theorem castSucc_mem_erase (i : Fin s) : Fin.castSucc i ∈ (univ : Finset (Fin (s + 1))).erase (Fin.last s) :=
  Finset.mem_erase.2 ⟨(Fin.castSucc_lt_last i).ne, Finset.mem_univ _⟩

variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)

theorem x_lift (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s),
      ∃ h ∈ Y p (setLast LL o) J M, resL p (Fin.last K, Fin.last s) 0 h = x :=
  restriction_surjective omega_injective_holds LL J M (Fin.last s) (by omega) (by simp) hv (tp_exists LL hs) o

theorem u_y (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (a : Fin (s + 1)) (o : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by
  intro h hh
  rw [mem_y] at hh ⊢
  refine ⟨raising_degree_holds p K (s + 1) LL c univ a o h hh.1, fun k => ?_⟩
  by_cases hk : K + 1 ≤ J k
  · have h1 : h ∈ YCond p LL (K + 1) ((c : ℤ) : WithTop ℤ) := by
      have := hh.2 k0
      rw [ycond_late _ (J k0) hk0, hc] at this
      exact this
    rw [ycond_late _ (J k) hk]
    exact ycond_mono LL (K + 1) _ _ (hc ▸ hmin k hk) (raising_keeps_last_letter p K (s + 1) LL c a hv h h1)
  · exact raising_keeps_early_letters p K (s + 1) LL c univ a (J k) (M k) (by omega) h (hh.2 k)

theorem u_x (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (i : Fin s) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s),
      Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i) x ∈ XSp p (setLast LL (o + 1)) J M (Fin.last s) := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := x_lift LL J M hs hv o x hx
  have e := restriction_raising_holds p K (s + 1) LL c (Fin.last s) (Fin.castSucc i) h (Fin.castSucc_lt_last i).ne
  rw [resL_apply, ← e]
  exact restriction_mem_space (setLast LL (o + 1)) J M (Fin.last s) (by omega) (by simp) hv (tp_exists _ hs) _
    (u_y LL J M c hv k0 hk0 hc hmin _ o h hh)

theorem gl_action_preserves_space (i j : Fin s) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s),
      glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) x ∈ XSp p (setLast LL o) J M (Fin.last s) := by
  intro x hx
  rw [mem_xsp] at hx ⊢
  obtain ⟨hxP, hxF, hxk⟩ := hx
  refine ⟨Formalism.CountingSumsFrames.glAct_pol (setLast LL o) (K + 1) _ _ x hxP,
    glAct_free LL (K + 1) _ _ (Fin.last K, Fin.last s) (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne x hxF,
    fun k => ⟨fun hk => ⟨?_, ?_⟩, fun hk => ?_⟩⟩
  · exact ycond_glAct_le (setLast LL o) (Nat.le_succ K) (M k) _ _ ((hxk k).1 hk).1
  · exact typesLE_glStable (setLast LL o) (K + 1) _ (M k) _ _ (castSucc_mem_erase i) (castSucc_mem_erase j) x
      ((hxk k).1 hk).2
  · exact ycond_glAct_le (setLast LL o) (by omega) (M k) _ _ ((hxk k).2 hk)

theorem derivative_lowers_degree (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (j : Fin s) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL (o + 1)) J M (Fin.last s),
      dW p K (Fin.castSucc j) x ∈ XSp p (setLast LL o) J M (Fin.last s) :=
  pderiv_last_letter_mem LL J M (Fin.last s) (Fin.castSucc j) o (by omega) (by simp) hv (tp_exists LL hs)
    (Fin.castSucc_lt_last j).ne

theorem derivative_kills_degree_zero (a : Fin (s + 1)) : ∀ x ∈ XSp p (setLast LL 0) J M (Fin.last s), dW p K a x = 0 := by
  intro x hx
  simp only [XSp, Submodule.mem_inf] at hx
  have hP := hx.1.1
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hP
  show pderiv (Fin.last K, a) x = 0
  have hnv : (Fin.last K, a) ∉ x.vars := by
    rw [MvPolynomial.mem_vars]
    rintro ⟨d, hd, hda⟩
    have h1 : MultiDeg (setLast LL 0) d := hP hd
    have h2 : ∑ b, d (Fin.last K, b) = 0 := by simpa [setLast] using h1 (Fin.last K)
    exact (Finsupp.mem_support_iff.1 hda) (Finset.sum_eq_zero_iff.1 h2 a (Finset.mem_univ _))
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hnv
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars hnv

theorem euler_last_letter_eigen (o : ℕ) : ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s), eulW p K (s + 1) x = ((o : ℕ) : ℚ_[p]) • x := by
  intro x hx
  simp only [XSp, Submodule.mem_inf] at hx
  rw [eulW_eq]
  have h := (pol_iff_eul (setLast LL o) x).1 hx.1.1 (Fin.last K)
  have hd : (setLast LL o).deg (Fin.last K) = o := by simp [setLast]
  rw [hd] at h
  exact h

theorem mem_wtot (o : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p])
    (hx : x ∈ XSp p (setLast LL o) J M (Fin.last s)) : x ∈ Wtot p LL J M (Fin.last s) := by
  unfold Wtot
  exact Submodule.mem_iSup_of_mem o hx

theorem wtot_stable (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c) :
    G.Stable (Wtot p LL J M (Fin.last s)) := by
  intro a b x hx
  rw [hE]
  have key : ∀ o : ℕ, ∀ y ∈ XSp p (setLast LL o) J M (Fin.last s),
      EX p LL c a b y ∈ Wtot p LL J M (Fin.last s) := by
    intro o y hy
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero =>
        rw [EX_zero_zero]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        rw [euler_last_letter_eigen LL J M o y hy]
        exact mem_wtot LL J M o _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hy))
      | succ j =>
        rw [EX_zero_succ]
        cases o with
        | zero =>
          rw [derivative_kills_degree_zero LL J M (Fin.castSucc j) y hy]
          exact Submodule.zero_mem _
        | succ o => exact mem_wtot LL J M o _ (derivative_lowers_degree LL J M hs hv j o y hy)
    | succ i =>
      induction b using Fin.cases with
      | zero =>
        rw [EX_succ_zero]
        exact mem_wtot LL J M (o + 1) _ (u_x LL J M c hs hv k0 hk0 hc hmin i o y hy)
      | succ j =>
        rw [EX_succ_succ]
        exact mem_wtot LL J M o _ (gl_action_preserves_space LL J M i j o y hy)
  have hle : (⨆ o : ℕ, XSp p (setLast LL o) J M (Fin.last s)) ≤
      (Wtot p LL J M (Fin.last s)).comap (EX p LL c a b) :=
    iSup_le fun o y hy => key o y hy
  have hx' : x ∈ ⨆ o : ℕ, XSp p (setLast LL o) J M (Fin.last s) := hx
  exact hle hx'

theorem x_vanish (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (o : ℕ) (ho : c + dEarly LL < o) :
    XSp p (setLast LL o) J M (Fin.last s) = ⊥ := by
  rw [eq_bot_iff, ← space_vanishing_holds p K (s + 1) LL (Fin.last s) c o (by omega) (by simp) hv ho]
  intro x hx
  have hx' := (mem_xsp _ J M _ x).mp hx
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hx'.1, hx'.2.1⟩, ?_⟩
  rw [← hc]
  exact ((hx'.2.2 k0).1 hk0).2

theorem wtot_monomial (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) :
    ∀ x ∈ Wtot p LL J M (Fin.last s), ∀ m ∈ x.support, ∃ o : ℕ, (o : ℤ) ≤ c + dEarly LL ∧ MultiDeg (setLast LL o) m := by
  have hle : Wtot p LL J M (Fin.last s) ≤ MvPolynomial.restrictSupport ℚ_[p]
      {m | ∃ o : ℕ, (o : ℤ) ≤ c + dEarly LL ∧ MultiDeg (setLast LL o) m} := by
    unfold Wtot
    refine iSup_le fun o => ?_
    by_cases ho : c + dEarly LL < o
    · rw [x_vanish LL J M c hs hv k0 hk0 hc o ho]
      exact bot_le
    · push_neg at ho
      intro y hy
      simp only [XSp, Submodule.mem_inf] at hy
      have hP := hy.1.1
      rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hP
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro m hm
      exact ⟨o, ho, hP hm⟩
  intro x hx m hm
  have h := hle hx
  rw [MvPolynomial.mem_restrictSupport_iff] at h
  exact h hm

theorem wtot_fd (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) : FiniteDimensional ℚ_[p] (Wtot p LL J M (Fin.last s)) := by
  have hle : Wtot p LL J M (Fin.last s) ≤
      ⨆ o : Fin ((c + dEarly LL).toNat + 1), Pol p (s + 1) (setLast LL o) := by
    unfold Wtot
    refine iSup_le fun o => ?_
    by_cases ho : c + dEarly LL < o
    · rw [x_vanish LL J M c hs hv k0 hk0 hc o ho]
      exact bot_le
    · push_neg at ho
      have h1 := Int.self_le_toNat (c + dEarly LL)
      have h2 : (o : ℤ) ≤ ((c + dEarly LL).toNat : ℤ) := le_trans ho h1
      have h3 : o ≤ (c + dEarly LL).toNat := by exact_mod_cast h2
      have hlt : o < (c + dEarly LL).toNat + 1 := by omega
      refine le_trans ?_ (le_iSup (fun o : Fin ((c + dEarly LL).toNat + 1) => Pol p (s + 1) (setLast LL o)) ⟨o, hlt⟩)
      intro x hx
      simp only [XSp, Submodule.mem_inf] at hx
      exact hx.1.1
  haveI : ∀ o : Fin ((c + dEarly LL).toNat + 1), FiniteDimensional ℚ_[p] (Pol p (s + 1) (setLast LL o)) :=
    fun o => pol_fd _
  exact Submodule.finiteDimensional_of_le hle

theorem isWt_supp (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0)
    (μ : Fin (s + 1) → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hx : G.IsWt μ x) :
    ∀ m ∈ x.support, wtX LL c m = μ := by
  intro m hm
  by_contra hne
  have hx' : G.comp μ x = x := hx
  have h1 := hcomp μ x m
  rw [hx', if_neg hne] at h1
  exact (MvPolynomial.mem_support_iff.1 hm) h1

private theorem mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen {K r : ℕ} (LL : Letters (K + 1)) (m : Fin (K + 1) × Fin r →₀ ℕ) (c' : Fin r)
    (hv : LL.vec (Fin.last K) = true) (o : ℕ) (hm : MultiDeg (setLast LL o) m) :
    -dEarly LL ≤ ∑ i : Fin (K + 1), (if LL.vec i = true then (m (i, c') : ℤ) else -(m (i, c') : ℤ)) ∧
      ∑ i : Fin (K + 1), (if LL.vec i = true then (m (i, c') : ℤ) else -(m (i, c') : ℤ)) ≤ dEarly LL + o := by
  have hle : ∀ j : Fin K, m (Fin.castSucc j, c') ≤ LL.deg (Fin.castSucc j) := by
    intro j
    have hs : ∑ a, m (Fin.castSucc j, a) = LL.deg (Fin.castSucc j) := by
      have h := hm (Fin.castSucc j)
      simpa [setLast, Function.update_apply, (Fin.castSucc_lt_last j).ne] using h
    rw [← hs]
    exact Finset.single_le_sum (f := fun a => m (Fin.castSucc j, a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')
  have hlo : m (Fin.last K, c') ≤ o := by
    have hs : ∑ a, m (Fin.last K, a) = o := by
      have h := hm (Fin.last K)
      simpa [setLast] using h
    rw [← hs]
    exact Finset.single_le_sum (f := fun a => m (Fin.last K, a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c')
  have hdE : dEarly LL = ∑ j : Fin K, (LL.deg (Fin.castSucc j) : ℤ) := by
    unfold dEarly
    rw [Fin.sum_univ_castSucc, if_pos rfl, add_zero]
    exact Finset.sum_congr rfl fun j _ => if_neg (Fin.castSucc_lt_last j).ne
  rw [hdE, Fin.sum_univ_castSucc, hv, if_pos rfl]
  have h1 : ∀ j : Fin K, -(LL.deg (Fin.castSucc j) : ℤ) ≤
      (if LL.vec (Fin.castSucc j) = true then (m (Fin.castSucc j, c') : ℤ) else -(m (Fin.castSucc j, c') : ℤ)) := by
    intro j
    have := hle j
    split_ifs <;> omega
  have h2 : ∀ j : Fin K,
      (if LL.vec (Fin.castSucc j) = true then (m (Fin.castSucc j, c') : ℤ) else -(m (Fin.castSucc j, c') : ℤ)) ≤
        (LL.deg (Fin.castSucc j) : ℤ) := by
    intro j
    have := hle j
    split_ifs <;> omega
  have s1 := Finset.sum_le_sum (s := univ) fun j _ => h1 j
  have s2 := Finset.sum_le_sum (s := univ) fun j _ => h2 j
  rw [Finset.sum_neg_distrib] at s1
  have h3 : (0 : ℤ) ≤ m (Fin.last K, c') := by positivity
  have h4 : (m (Fin.last K, c') : ℤ) ≤ o := by exact_mod_cast hlo
  constructor <;> linarith

theorem wtX_range (hv : LL.vec (Fin.last K) = true) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) (o : ℕ)
    (ho : (o : ℤ) ≤ c + dEarly LL) (hm : MultiDeg (setLast LL o) m) (i : Fin (s + 1)) :
    -dEarly LL ≤ wtX LL c m i ∧ wtX LL c m i ≤ 2 * dEarly LL + c := by
  have hd0 := dEarly_nonneg LL
  induction i using Fin.cases with
  | zero =>
    simp only [wtX, Fin.cases_zero]
    have h := hm (Fin.last K)
    have hl : ∑ a, m (Fin.last K, a) = o := by simpa [setLast] using h
    have hz : (∑ a, (m (Fin.last K, a) : ℤ)) = (o : ℤ) := by exact_mod_cast hl
    rw [hz]
    constructor <;> omega
  | succ i' =>
    simp only [wtX, Fin.cases_succ, wt, Fin.is_lt, ↓reduceIte]
    have h := mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen LL m (Fin.castSucc i') hv o hm
    constructor <;> linarith [h.1, h.2]

theorem wtot_bound (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hcd : c < LL.total)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    ∀ (μ ν : Fin (s + 1) → ℤ) (x y : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ Wtot p LL J M (Fin.last s) → y ∈ Wtot p LL J M (Fin.last s) → G.IsWt μ x → G.IsWt ν y →
      ∀ i, |ν i - μ i| ≤ ((4 * LL.total : ℕ) : ℤ) := by
  intro μ ν x y hx0 hy0 hxW hyW hxw hyw i
  obtain ⟨mx, hmx⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 hx0)
  obtain ⟨my, hmy⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 hy0)
  have hwx := isWt_supp LL c G hcomp μ x hxw mx hmx
  have hwy := isWt_supp LL c G hcomp ν y hyw my hmy
  obtain ⟨ox, hox, hmdx⟩ := wtot_monomial LL J M c hs hv k0 hk0 hc x hxW mx hmx
  obtain ⟨oy, hoy, hmdy⟩ := wtot_monomial LL J M c hs hv k0 hk0 hc y hyW my hmy
  have rx := wtX_range LL c hv mx ox hox hmdx i
  have ry := wtX_range LL c hv my oy hoy hmdy i
  rw [hwx] at rx
  rw [hwy] at ry
  have h1 := dEarly_le_total LL
  have h0 := dEarly_nonneg LL
  rw [abs_le]
  push_cast
  constructor <;> linarith [rx.1, rx.2, ry.1, ry.2]

theorem wtot_finW (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ))
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    G.FinW (Wtot p LL J M (Fin.last s)) := by
  refine ⟨Fintype.piFinset fun _ => Finset.Icc (-dEarly LL) (2 * dEarly LL + c), ?_⟩
  intro x hx μ hμ
  by_contra hne
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 hne)
  have h1 := hcomp μ x m
  have hcm : coeff m (G.comp μ x) ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  by_cases hw : wtX LL c m = μ
  · rw [if_pos hw] at h1
    have hmx : m ∈ x.support := MvPolynomial.mem_support_iff.2 (by rwa [h1] at hcm)
    obtain ⟨o, ho, hmd⟩ := wtot_monomial LL J M c hs hv k0 hk0 hc x hx m hmx
    apply hμ
    rw [Fintype.mem_piFinset]
    intro i
    have r := wtX_range LL c hv m o ho hmd i
    rw [hw] at r
    exact Finset.mem_Icc.2 r
  · rw [if_neg hw] at h1
    exact hcm h1

theorem latData (hU : UDivInt) (hD : DWDivInt) (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q)
    (hk0 : K + 1 ≤ J k0) (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (hcd : c < LL.total)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    LatData p G (Wtot p LL J M (Fin.last s)) (IntPol p (Fin (K + 1) × Fin (s + 1))).toAddSubgroup (4 * LL.total) where
  stable := wtot_stable LL J M c hs hv k0 hk0 hc hmin G hE
  fd := wtot_fd LL J M c hs hv k0 hk0 hc
  finW := wtot_finW LL J M c hs hv k0 hk0 hc G hcomp
  bound := wtot_bound LL J M c hs hv k0 hk0 hc hcd G hcomp
  closed := fun a ha x hx => smul_int a ha x hx
  div := by
    rw [hE]
    intro a b hab k x hx
    show _ ∈ IntPol p (Fin (K + 1) × Fin (s + 1))
    have hx' : x ∈ IntPol p (Fin (K + 1) × Fin (s + 1)) := hx
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact absurd rfl hab
      · rw [EX_zero_succ]
        exact hD p K (s + 1) (Fin.castSucc j) k x hx'
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · rw [EX_succ_zero]
        exact hU p K (s + 1) LL c _ (Fin.castSucc i) k (castSucc_mem_erase i) x hx'
      · rw [EX_succ_succ]
        refine Formalism.InvariantFactorPaths.PW.Top.divInt p (K + 1) (s + 1) LL (K + 1) _ _ (fun h => hab ?_) k x hx'
        rw [Fin.castSucc_injective s h]
  graded := by
    intro μ x hx
    show _ ∈ IntPol p (Fin (K + 1) × Fin (s + 1))
    have hx' : x ∈ IntPol p (Fin (K + 1) × Fin (s + 1)) := hx
    rw [intPol_iff_norm] at hx' ⊢
    intro m
    rw [hcomp]
    split_ifs
    · exact hx' m
    · simp
  basis := by
    intro U hUW
    have := wtot_fd (p := p) LL J M c hs hv k0 hk0 hc
    exact Formalism.InvariantFactorPaths.PW.Top.latBasisPol p _ U (Submodule.finiteDimensional_of_le hUW)

theorem wtot_le_iso (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q)
    (hk0 : K + 1 ≤ J k0) (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    Wtot p LL J M (Fin.last s) ≤ ⨆ la, IsoW G (Wtot p LL J M (Fin.last s)) la := by
  obtain ⟨S, hS⟩ := wtot_finW LL J M c hs hv k0 hk0 hc G hcomp
  have hst := wtot_stable LL J M c hs hv k0 hk0 hc hmin G hE
  let ι := {z : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p] × (Fin (s + 1) → ℤ) //
    G.IsHW z.2 z.1 ∧ z.1 ∈ Wtot p LL J M (Fin.last s) ∧ z.1 ≠ 0}
  have h1 := GlX.span_hw G hst hS (ι := ι) (fun z => z.1.1) (fun z => z.1.2) (fun z => z.2.1) (fun z => z.2.2.1)
    (fun z => z.2.2.2) (by
      intro μ v hvW hvh
      by_cases hv0 : v = 0
      · rw [hv0]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨(v, μ), hvh, hvW, hv0⟩, rfl⟩)
  refine h1.trans (iSup_le fun z => le_iSup_of_le z.1.2 ?_)
  refine G.gS_le ?_ (G.gS_stable _)
  intro v hv'
  rw [Set.mem_singleton_iff] at hv'
  rw [hv']
  exact G.subset_gS _ ⟨z.2.1, z.2.2.1⟩

theorem hw_deg_zero (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0)
    (la : Fin (s + 1) → ℤ) (h : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hh : G.IsHW la h)
    (hW : h ∈ Wtot p LL J M (Fin.last s)) : h ∈ XSp p (setLast LL 0) J M (Fin.last s) := by
  by_cases h0 : h = 0
  · rw [h0]; exact Submodule.zero_mem _
  obtain ⟨m0, hm0⟩ : h.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h' => h0 (support_eq_empty.mp h')
  obtain ⟨o0, ho0⟩ : ∃ o0 : ℕ, o0 = ∑ a : Fin (s + 1), m0 (Fin.last K, a) := ⟨_, rfl⟩
  have hdeg : ∀ m ∈ h.support, ∑ a : Fin (s + 1), m (Fin.last K, a) = o0 := by
    intro m hm
    have h1 := congrFun (isWt_supp LL c G hcomp la h hh.1 m hm) 0
    have h2 := congrFun (isWt_supp LL c G hcomp la h hh.1 m0 hm0) 0
    have h3 : c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ) = c - ∑ a : Fin (s + 1), (m0 (Fin.last K, a) : ℤ) :=
      h1.trans h2.symm
    have h4 : ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ) = ∑ a : Fin (s + 1), (m0 (Fin.last K, a) : ℤ) := by linarith
    rw [ho0]
    exact_mod_cast h4
  let Pr : (Fin (K + 1) × Fin (s + 1) →₀ ℕ) → Prop := fun m => ∑ a : Fin (s + 1), m (Fin.last K, a) = o0
  have hfix : compL ℚ_[p] Pr h = h := compL_of_mem Pr h (by
    rw [mem_restrictSupport_iff]
    intro m hm
    exact hdeg m (Finset.mem_coe.mp hm))
  have hall : Wtot p LL J M (Fin.last s) ≤ (XSp p (setLast LL o0) J M (Fin.last s)).comap (compL ℚ_[p] Pr) := by
    refine iSup_le fun o x hx => ?_
    show compL ℚ_[p] Pr x ∈ XSp p (setLast LL o0) J M (Fin.last s)
    have hxP := ((mem_xsp _ J M _ x).mp hx).1
    rw [Pol, mem_restrictSupport_iff] at hxP
    have hl : ∀ m ∈ x.support, ∑ a : Fin (s + 1), m (Fin.last K, a) = o := fun m hm => by
      have := hxP (Finset.mem_coe.mpr hm) (Fin.last K)
      simpa [setLast] using this
    by_cases ho : o = o0
    · subst ho
      rw [compL_of_mem Pr x (by
        rw [mem_restrictSupport_iff]
        intro m hm
        exact hl m (Finset.mem_coe.mp hm))]
      exact hx
    · rw [compL_of_not Pr x (by
        rw [mem_restrictSupport_iff]
        intro m hm
        show ¬ (∑ a : Fin (s + 1), m (Fin.last K, a) = o0)
        rw [hl m (Finset.mem_coe.mp hm)]
        exact ho)]
      exact Submodule.zero_mem _
  have hX : h ∈ XSp p (setLast LL o0) J M (Fin.last s) := by
    have := hall hW
    rwa [Submodule.mem_comap, hfix] at this
  have hF := ((mem_xsp _ J M _ h).mp hX).2.1
  have e1 := euler_last_letter_eigen LL J M o0 h hX
  have e2 : eulW p K (s + 1) h = 0 := by
    rw [eulW_eq, ProjS.eulL_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    have e3 : pderiv (Fin.last K, a) h = 0 := by
      refine Fin.lastCases ?_ (fun j => ?_) a
      · exact pderiv_free _ h hF
      · have h5 := hh.2 0 j.succ (Fin.succ_pos j)
        rw [hE, EX_zero_succ] at h5
        exact h5
    rw [e3, mul_zero]
  rw [e2] at e1
  have h6 : ((o0 : ℕ) : ℚ_[p]) = 0 := (smul_eq_zero.mp e1.symm).resolve_right h0
  have h7 : o0 = 0 := Nat.cast_eq_zero.mp h6
  rw [h7] at hX
  exact hX

end LatW

end Formalism.InvariantFactorPaths.L4
