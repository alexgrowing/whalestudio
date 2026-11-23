import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootNormSubPowLe

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
open Polynomial

namespace GlobalTheory.AxLemma

section General
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_taylor_coeff_le (T : Finset K) (x : K) (r : ℝ) (hr : 0 ≤ r) (h : ∀ z ∈ T, ‖z - x‖ ≤ r)
    (q : ℕ) (hq : q ≤ T.card) :
    ‖(hasseDeriv q (∏ z ∈ T, (X - C z))).eval x‖ ≤ r ^ (T.card - q) := by
  rw [← taylor_coeff]
  have h1 : taylor x (∏ z ∈ T, (X - C z)) = ∏ z ∈ T, (X + C (x - z)) := by
    rw [taylor_apply, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun z _ => ?_
    simp only [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [h1, Finset.prod_X_add_C_coeff T _ hq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  rw [norm_prod, ← ht.2, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun z hz => ?_
  rw [norm_sub_rev]
  exact h z (ht.1 hz)

omit [IsUltrametricDist K] in
theorem exists_root_near [IsAlgClosed K] (p : K[X]) (hp : 0 < p.natDegree) (x : K) :
    ∃ b ∈ p.roots, ‖p.leadingCoeff‖ * ‖b - x‖ ^ p.natDegree ≤ ‖p.eval x‖ := by
  first
  | exact @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | (apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le ..)

end General

variable {l : ℕ} [Fact l.Prime]

theorem norm_gal' (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := (spectralNorm_eq_of_equiv g x).symm

theorem one_le_mul_norm_choose (n q : ℕ) (hn : 0 < n) (hq : q ≤ n) :
    1 ≤ (n : ℝ) * ‖((n.choose q : ℕ) : Om l)‖ := by
  have hl : l.Prime := Fact.out
  have h0 : n.choose q ≠ 0 := (Nat.choose_pos hq).ne'
  have h1 : ((n.choose q : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) ((n.choose q : ℕ) : ℚ_[l]) := by
    rw [map_natCast]
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0),
    Padic.valuation_natCast, zpow_neg, zpow_natCast]
  have h2 := Nat.pow_factorization_choose_le (p := l) (k := q) hn
  rw [Nat.factorization_def _ hl] at h2
  have h3 : (0 : ℝ) < (l : ℝ) ^ padicValNat l (n.choose q) := by
    have := hl.pos
    positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h3, one_mul]
  exact_mod_cast h2

noncomputable def cst (k : ℕ) : ℝ := (2 : ℝ) ^ ((4 : ℝ) - (2 * k + 4) / 2 ^ k)

noncomputable def loss (k : ℕ) : ℝ := (2 : ℝ) ^ (((k : ℝ) + 1) / 2 ^ k)

theorem cst_succ (k : ℕ) : cst (k + 1) = cst k * loss k := by
  unfold cst loss
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  field_simp
  ring

theorem one_le_loss (k : ℕ) : 1 ≤ loss k :=
  Real.one_le_rpow (by norm_num) (by positivity)

theorem loss_pow (k : ℕ) : loss k ^ (2 ^ k) = 2 ^ (k + 1) := by
  unfold loss
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast (2 : ℝ) (k + 1)]
  congr 1
  push_cast
  field_simp

theorem one_le_cst (k : ℕ) : 1 ≤ cst k := by
  induction k with
  | zero => simp [cst]
  | succ k ih => rw [cst_succ]; exact one_le_mul_of_one_le_of_one_le ih (one_le_loss k)

theorem cst_le (k : ℕ) : cst k ≤ 16 := by
  unfold cst
  have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
  rw [this]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (2 * k + 4) / 2 ^ k := by positivity
  linarith

theorem ax_step (H : Subgroup (GQ l)) (k : ℕ) : ∀ (x : Om l) (r : ℝ) (S : Finset (Om l)),
    (∀ g ∈ H, g x ∈ S) → S.card ≤ 2 ^ k → (∀ g ∈ H, ‖g x - x‖ ≤ r) →
    ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ cst k * r := by
  classical
  induction k with
  | zero =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    refine ⟨x, fun g hg => ?_, ?_⟩
    · have hx : x ∈ S := by simpa using hS 1 H.one_mem
      exact Finset.card_le_one.1 (by simpa using hc) _ (hS g hg) _ hx
    · have := one_le_cst 0
      rw [sub_self, norm_zero]; positivity
  | succ k ih =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    have hc1 := one_le_cst k
    have hl1 := one_le_loss k
    set T := S.filter (fun z => ∃ g ∈ H, g x = z) with hT
    have hTm : ∀ z, z ∈ T ↔ ∃ g ∈ H, g x = z := by
      intro z
      rw [hT, Finset.mem_filter]
      exact ⟨fun h => h.2, fun ⟨g, hg, h⟩ => ⟨h ▸ hS g hg, g, hg, h⟩⟩
    have hTc : T.card ≤ 2 ^ (k + 1) := (Finset.card_filter_le _ _).trans hc
    by_cases hk : T.card ≤ 2 ^ k
    · obtain ⟨y, hy, hxy⟩ := ih x r T (fun g hg => (hTm _).2 ⟨g, hg, rfl⟩) hk hr
      refine ⟨y, hy, hxy.trans ?_⟩
      rw [cst_succ]
      refine mul_le_mul_of_nonneg_right ?_ hr0
      nlinarith
    push Not at hk
    set f : (Om l)[X] := ∏ z ∈ T, (X - C z) with hf
    set q := T.card - 2 ^ k with hq
    have hq1 : T.card - q = 2 ^ k := by omega
    have hfm : f.Monic := monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z
    have hfd : f.natDegree = T.card := by
      rw [hf, natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]; simp
    have hfg : ∀ g ∈ H, f.map (g : Om l →+* Om l) = f := by
      intro g hg
      rw [hf, Polynomial.map_prod]
      refine Finset.prod_bij (fun z _ => g z) ?_ ?_ ?_ ?_
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        exact (hTm _).2 ⟨g * g', H.mul_mem hg hg', rfl⟩
      · intro a _ b _ h
        exact g.injective h
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        refine ⟨(g⁻¹ * g') x, (hTm _).2 ⟨_, H.mul_mem (H.inv_mem hg) hg', rfl⟩, ?_⟩
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
      · intro z _
        simp
    set p := hasseDeriv q f with hp
    have hpd : p.natDegree = 2 ^ k := by rw [hp, natDegree_hasseDeriv, hfd, hq1]
    have hpl : p.leadingCoeff = ((T.card.choose q : ℕ) : Om l) := by
      have h2 : 2 ^ k + q = T.card := by omega
      rw [leadingCoeff, hpd, hp, hasseDeriv_coeff, h2]
      conv_lhs => rw [← hfd, hfm.coeff_natDegree, hfd]
      rw [mul_one]
    have hpg : ∀ g ∈ H, p.map (g : Om l →+* Om l) = p := by
      intro g hg
      ext n
      have := congrArg (fun u => coeff u (n + q)) (hfg g hg)
      simp only [coeff_map] at this
      rw [coeff_map, hp, hasseDeriv_coeff, map_mul, map_natCast, this]
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hpd
      exact (pow_pos two_pos k).ne hpd
    obtain ⟨b, hb, hbx⟩ := exists_root_near p (by rw [hpd]; positivity) x
    have hev := norm_taylor_coeff_le T x r hr0 (fun z hz => by
      obtain ⟨g, hg, rfl⟩ := (hTm z).1 hz
      exact hr g hg) q (by omega)
    rw [← hf, ← hp, hq1] at hev
    rw [hpd, hpl] at hbx
    have hch := one_le_mul_norm_choose (l := l) T.card q (by omega) (by omega)
    have hbr : ‖b - x‖ ≤ loss k * r := by
      refine le_of_pow_le_pow_left₀ (pow_pos two_pos k).ne' (by positivity) ?_
      rw [mul_pow, loss_pow]
      have h1 : (T.card : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hTc
      have h2 : 0 ≤ ‖b - x‖ ^ 2 ^ k := by positivity
      have h3 : (0 : ℝ) ≤ T.card := by positivity
      calc ‖b - x‖ ^ 2 ^ k ≤ (T.card * ‖((T.card.choose q : ℕ) : Om l)‖) * ‖b - x‖ ^ 2 ^ k :=
            le_mul_of_one_le_left h2 hch
        _ ≤ T.card * r ^ 2 ^ k := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbx.trans hev) h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hrr : r ≤ loss k * r := le_mul_of_one_le_left hr0 hl1
    have hgb : ∀ g ∈ H, ‖g b - b‖ ≤ loss k * r := by
      intro g hg
      have e : g b - b = g (b - x) + ((g x - x) + (x - b)) := by rw [map_sub]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · rw [norm_gal']; exact hbr
      · exact (hr g hg).trans hrr
      · rw [norm_sub_rev]; exact hbr
    obtain ⟨y, hy, hby⟩ := ih b (loss k * r) p.roots.toFinset (fun g hg => by
      rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
      have h0 : p.eval b = 0 := (mem_roots hp0).1 hb
      have h1 := eval_map_apply (g : Om l →+* Om l) (p := p) b
      rw [hpg g hg, h0, map_zero] at h1
      exact h1)
      ((Multiset.toFinset_card_le _).trans ((card_roots' p).trans hpd.le)) hgb
    refine ⟨y, hy, ?_⟩
    have e : x - y = (x - b) + (b - y) := by ring
    rw [e, cst_succ, mul_assoc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hby)
    rw [norm_sub_rev]
    exact hbr.trans (le_mul_of_one_le_left (by positivity) hc1)

theorem ax_lemma : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ),
    (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  classical
  intro l _
  refine ⟨16, by norm_num, fun H x r hr => ?_⟩
  have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set S := ((minpoly ℚ_[l] x).aroots (Om l)).toFinset with hS
  obtain ⟨y, hy, hxy⟩ := ax_step H S.card x r S (fun g _ => by
    rw [hS, Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]) Nat.lt_two_pow_self.le hr
  exact ⟨y, hy, hxy.trans (mul_le_mul_of_nonneg_right (cst_le _) hr0)⟩

end GlobalTheory.AxLemma
