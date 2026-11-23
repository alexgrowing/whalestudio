import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableAtGP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower

noncomputable section

open scoped UpperHalfPlane MatrixGroups Topology
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.SiegQ GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model Filter

namespace GlobalTheory.SiegTwo

def jets (M : ℕ) (A : ℤ) (v : ℂ) (s : ℤ) : AddSubgroup (ℂ × ℂ) :=
  AddSubgroup.closure {x | ∃ k : ℤ, (M : ℤ) ∣ s - A * k ∧ x = (v ^ k, k * v ^ k)}

def dm (x y : ℂ × ℂ) : ℂ × ℂ := (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

variable {M : ℕ} {A : ℤ} {v : ℂ}

theorem gen_mem {s k : ℤ} (h : (M : ℤ) ∣ s - A * k) : (v ^ k, k * v ^ k) ∈ jets M A v s :=
  AddSubgroup.subset_closure ⟨k, h, rfl⟩

theorem dm_mem (hv : v ≠ 0) {s t : ℤ} {x y : ℂ × ℂ} (hx : x ∈ jets M A v s) (hy : y ∈ jets M A v t) :
    dm x y ∈ jets M A v (s + t) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      have h : (M : ℤ) ∣ s + t - A * (k + l) := by
        have := dvd_add hk hl
        rwa [show s - A * k + (t - A * l) = s + t - A * (k + l) by ring] at this
      convert gen_mem (v := v) h using 1
      simp only [dm, zpow_add₀ hv]
      push_cast
      congr 1
      ring
    | zero => simp only [dm, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]; exact zero_mem (jets M A v (s + t))
    | add y y' _ _ h1 h2 => convert add_mem h1 h2 using 1; simp only [dm, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; congr 1 <;> ring
    | neg y _ h1 => convert neg_mem h1 using 1; simp only [dm, Prod.neg_mk, Prod.fst_neg, Prod.snd_neg]; congr 1 <;> ring
  | zero => simp only [dm, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]; exact zero_mem (jets M A v (s + t))
  | add y y' _ _ h1 h2 => convert add_mem h1 h2 using 1; simp only [dm, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; congr 1 <;> ring
  | neg y _ h1 => convert neg_mem h1 using 1; simp only [dm, Prod.neg_mk, Prod.fst_neg, Prod.snd_neg]; congr 1 <;> ring

theorem exists_finsupp {s : ℤ} {x : ℂ × ℂ} (hx : x ∈ jets M A v s) :
    ∃ θ : ℤ →₀ ℤ, (∀ k, θ k ≠ 0 → (M : ℤ) ∣ s - A * k) ∧ x.1 = θ.sum (fun k n => (n : ℂ) * v ^ k) ∧
      x.2 = θ.sum (fun k n => ((k * n : ℤ) : ℂ) * v ^ k) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Finsupp.single k 1, fun l hl => ?_, by simp, by simp⟩
    rwa [(Finsupp.single_apply_ne_zero.1 hl).1]
  | zero => exact ⟨0, by simp, by simp, by simp⟩
  | add y y' _ _ h1 h2 =>
    obtain ⟨θ, a1, a2, a3⟩ := h1
    obtain ⟨θ', b1, b2, b3⟩ := h2
    refine ⟨θ + θ', fun k hk => ?_, ?_, ?_⟩
    · by_cases h : θ k = 0
      · exact b1 k (by simpa [h] using hk)
      · exact a1 k h
    · rw [Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring), Prod.fst_add, a2, b2]
    · rw [Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring), Prod.snd_add, a3, b3]
  | neg y _ h1 =>
    obtain ⟨θ, a1, a2, a3⟩ := h1
    refine ⟨-θ, fun k hk => a1 k (by simpa using hk), ?_, ?_⟩
    · rw [Finsupp.sum_neg_index (by simp), Prod.fst_neg, a2]; simp [Finsupp.sum]
    · rw [Finsupp.sum_neg_index (by simp), Prod.snd_neg, a3]; simp [Finsupp.sum]

abbrev Hol (F : ℂ → ℂ) : Prop := DifferentiableOn ℂ F (Metric.ball 0 1)

theorem tc_add {F G : ℂ → ℂ} (hF : Hol F) (hG : Hol G) : tc (fun z => F z + G z) = fun n => tc F n + tc G n :=
  HasQ.coeff_unique one_pos (hasQ_tc (hF.add hG) one_pos) ((hasQ_tc hF one_pos).add (hasQ_tc hG one_pos))

def dc (U L : ℂ → ℂ) (n : ℕ) : ℂ × ℂ := (tc U n, tc (fun z => U z * L z) n)

theorem dc_mul {U L U' L' : ℂ → ℂ} (h1 : Hol U) (h2 : Hol L) (h3 : Hol U') (h4 : Hol L') (n : ℕ) :
    dc (fun z => U z * U' z) (fun z => L z + L' z) n =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, dm (dc U L p.1) (dc U' L' p.2) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, dc, dm, tc_mul h1 h3, conv]
  · have e : (fun z => U z * U' z * (L z + L' z)) = fun z => U z * (U' z * L' z) + (U z * L z) * U' z := by
      funext z; ring
    simp only [Prod.snd_sum, dc, dm, e]
    rw [tc_add (h1.fun_mul (h3.fun_mul h4)) ((h1.fun_mul h2).fun_mul h3), tc_mul h1 (h3.fun_mul h4),
      tc_mul (h1.fun_mul h2) h3]
    simp only [conv, Finset.sum_add_distrib]

theorem dc_one (n : ℕ) : dc (fun _ => 1) (fun _ => 0) n = if n = 0 then (1, 0) else 0 := by
  simp only [dc, tc_const]
  split_ifs <;> simp

theorem hol_frac {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ} (he : 0 < e) : Hol fun z => w * z ^ e / (1 - w * z ^ e) :=
  DifferentiableOn.div (by fun_prop) (by fun_prop) fun z hz => lin_ne_zero hw he (by simpa using hz)

theorem dc_lin {w : ℂ} (hw : ‖w‖ ≤ 1) (J : ℂ) {e : ℕ} (he : 0 < e) (n : ℕ) :
    dc (fun z => 1 - w * z ^ e) (fun z => -J * (w * z ^ e / (1 - w * z ^ e))) n =
      (if n = 0 then (1, 0) else 0) - if n = e then (w, J * w) else 0 := by
  have : tc (fun z => (1 - w * z ^ e) * (-J * (w * z ^ e / (1 - w * z ^ e)))) =
      tc (fun z => (1 - (J * w) * z ^ e) + -1) :=
    tc_congr fun z hz => by
      have := lin_ne_zero hw he hz
      field_simp
      ring
  simp only [dc, this]
  rw [tc_add (by unfold Hol; fun_prop) (by unfold Hol; fun_prop), tc_lin, tc_lin, tc_const]
  by_cases h0 : n = 0 <;> by_cases h1 : n = e <;> simp [h0, h1, he.ne, he.ne']

structure IsU (M : ℕ) (A : ℤ) (v : ℂ) (U L : ℂ → ℂ) : Prop where
  dU : Hol U
  dL : Hol L
  ne : ∀ z, ‖z‖ < 1 → U z ≠ 0
  U0 : U 0 = 1
  L0 : L 0 = 0
  mem : ∀ n : ℕ, dc U L n ∈ jets M A v n

theorem one_mem_jets : ((1, 0) : ℂ × ℂ) ∈ jets M A v 0 := by
  simpa using gen_mem (M := M) (A := A) (v := v) (s := 0) (k := 0) (by simp)

theorem IsU.one : IsU M A v (fun _ => 1) (fun _ => 0) :=
  ⟨differentiableOn_const _, differentiableOn_const _, by simp, rfl, rfl, fun n => by
    rw [dc_one]; split_ifs with h
    · subst h; exact one_mem_jets
    · exact zero_mem _⟩

theorem IsU.mul (hv : v ≠ 0) {U L U' L' : ℂ → ℂ} (h : IsU M A v U L) (h' : IsU M A v U' L') :
    IsU M A v (fun z => U z * U' z) (fun z => L z + L' z) :=
  ⟨h.dU.mul h'.dU, h.dL.add h'.dL, fun z hz => mul_ne_zero (h.ne z hz) (h'.ne z hz), by simp [h.U0, h'.U0],
    by simp [h.L0, h'.L0], fun n => by
    rw [dc_mul h.dU h.dL h'.dU h'.dL]
    refine sum_mem fun p hp => ?_
    have := dm_mem hv (h.mem p.1) (h'.mem p.2)
    rwa [← Nat.cast_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp] at this⟩

theorem IsU.inv (hv : v ≠ 0) {U L : ℂ → ℂ} (h : IsU M A v U L) : IsU M A v (fun z => (U z)⁻¹) (fun z => -L z) := by
  have hd : Hol fun z => (U z)⁻¹ := h.dU.inv fun z hz => h.ne z (by simpa using hz)
  refine ⟨hd, h.dL.neg, fun z hz => inv_ne_zero (h.ne z hz), by simp [h.U0], by simp [h.L0], fun n => ?_⟩
  have hc : ∀ n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, dm (dc U L p.1) (dc (fun z => (U z)⁻¹) (fun z => -L z) p.2) =
      if n = 0 then (1, 0) else 0 := fun n => by
    rw [← dc_mul h.dU h.dL hd h.dL.fun_neg, ← dc_one]
    simp only [dc]
    rw [tc_congr (G := fun _ => 1) fun z hz => mul_inv_cancel₀ (h.ne z hz)]
    simp
  have h0 : ∀ x, dm (dc U L 0) x = x := fun x => by simp [dm, dc, tc_zero, h.U0, h.L0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · have := hc 0
      simp only [Finset.HasAntidiagonal.antidiagonal_zero, Finset.sum_singleton, h0, if_true] at this
      rw [this]; exact one_mem_jets
    · have h1 := hc (n + 1)
      simp only [Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.sum_map, h0, Nat.succ_ne_zero, if_false] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      refine neg_mem (sum_mem fun p hp => ?_)
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have := dm_mem hv (h.mem (p.1 + 1)) (ih p.2 (by omega))
      rw [← Nat.cast_add, show p.1 + 1 + p.2 = n + 1 by omega] at this
      exact this

theorem IsU.lin (hv : ‖v‖ = 1) {j : ℤ} {e : ℕ} (he : 0 < e) (hd : (M : ℤ) ∣ e - A * j) :
    IsU M A v (fun z => 1 - v ^ j * z ^ e) (fun z => -j * (v ^ j * z ^ e / (1 - v ^ j * z ^ e))) := by
  have hw : ‖v ^ j‖ ≤ 1 := by simp [hv]
  refine ⟨by unfold Hol; fun_prop, (hol_frac hw he).const_mul _, fun z hz => lin_ne_zero hw he hz, by simp [he.ne'],
    by simp [he.ne'], fun n => ?_⟩
  rw [dc_lin hw _ he]
  refine sub_mem ?_ ?_ <;> split_ifs with h
  · subst h; exact one_mem_jets
  · exact zero_mem _
  · subst h; exact gen_mem hd
  · exact zero_mem _

theorem dc_mul_lin {U L : ℂ → ℂ} (h1 : Hol U) (h2 : Hol L) {w : ℂ} (hw : ‖w‖ ≤ 1) (J : ℂ) {e n : ℕ} (h : n < e) :
    dc (fun z => U z * (1 - w * z ^ e)) (fun z => L z + -J * (w * z ^ e / (1 - w * z ^ e))) n = dc U L n := by
  have he : 0 < e := by omega
  rw [dc_mul h1 h2 (by unfold Hol; fun_prop) ((hol_frac hw he).const_mul _), Finset.sum_eq_single (n, 0)]
  · rw [dc_lin hw J he]; simp [he.ne, dm]
  · intro p hp hne
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have h2 : p.2 ≠ 0 := fun h2 => hne (Prod.ext (by simp; omega) h2)
    rw [dc_lin hw J he]; simp [h2, show p.2 ≠ e by omega, dm]
  · simp

def lam (M : ℕ) (w : ℂ) (e : ℕ) (z : ℂ) : ℂ := ∑' m : ℕ, w * z ^ (e + m * M) / (1 - w * z ^ (e + m * M))

theorem lam_locUnif (hM : 0 < M) {w : ℂ} (hw : ‖w‖ ≤ 1) {e : ℕ} (he : 0 < e) :
    TendstoLocallyUniformlyOn (fun (N : ℕ) (z : ℂ) => ∑ m ∈ Finset.range N,
      w * z ^ (e + m * M) / (1 - w * z ^ (e + m * M))) (lam M w e) atTop (Metric.ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball]
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hN] using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
      (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
    have hq : ‖q₀‖ < 1 := by simpa using hK hq₀
    refine tendstoUniformlyOn_tsum_nat (u := fun m => ‖q₀‖ ^ (m + 1) / (1 - ‖q₀‖))
      (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)).div_const _)
      fun m x hx => ?_
    have h1 := norm_term_le hM hw he (HB x hx) hq m
    rw [norm_neg] at h1
    have h2 : ‖q₀‖ ^ (m + 1) ≤ ‖q₀‖ := pow_le_of_le_one (norm_nonneg _) hq.le (by omega)
    have h3 := norm_sub_norm_le (1 : ℂ) (w * x ^ (e + m * M))
    rw [norm_one] at h3
    rw [norm_div]
    gcongr
    linarith

theorem IsU.ep (hM : 0 < M) (hv : ‖v‖ = 1) {j : ℤ} {e : ℕ} (he : 0 < e) (hd : (M : ℤ) ∣ e - A * j) :
    IsU M A v (ep M (v ^ j) e) (fun z => -j * lam M (v ^ j) e z) := by
  have hw : ‖v ^ j‖ ≤ 1 := by simp [hv]
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  set w := v ^ j with hwd
  have h := (ep_locUnif hM hw he).tendstoLocallyUniformlyOn_finsetRange
  have h' := lam_locUnif hM hw he
  set F : ℕ → ℂ → ℂ := fun N z => ∏ m ∈ Finset.range N, (1 - w * z ^ (e + m * M)) with hF
  set G : ℕ → ℂ → ℂ := fun N z => ∑ m ∈ Finset.range N, w * z ^ (e + m * M) / (1 - w * z ^ (e + m * M)) with hG
  have e1 : ∀ N, F (N + 1) = fun z => F N z * (1 - w * z ^ (e + N * M)) := fun N => by
    funext z; simp only [hF, Finset.prod_range_succ]
  have e2 : ∀ N, (fun z => -j * G (N + 1) z) =
      fun z => -j * G N z + -j * (w * z ^ (e + N * M) / (1 - w * z ^ (e + N * M))) := fun N => by
    funext z; simp only [hG, Finset.sum_range_succ, mul_add]
  have hg : ∀ N, IsU M A v (F N) (fun z => -j * G N z) := fun N => by
    induction N with
    | zero => simpa [hF, hG] using IsU.one
    | succ N ih =>
      rw [e1, e2]
      refine ih.mul hv0 (IsU.lin hv (by omega) ?_)
      have := dvd_add hd (dvd_mul_left (M : ℤ) N)
      rwa [show e - A * j + N * (M : ℤ) = ((e + N * M : ℕ) : ℤ) - A * j by push_cast; ring] at this
  have hGd : ∀ N, Hol (G N) := fun N => DifferentiableOn.fun_sum fun m _ => hol_frac hw (by omega)
  have d1 : Hol (SiegQ.ep M w e) := h.differentiableOn (.of_forall fun N => (hg N).dU) Metric.isOpen_ball
  have d2 : Hol (lam M w e) := h'.differentiableOn (.of_forall hGd) Metric.isOpen_ball
  refine ⟨d1, d2.const_mul _, fun z hz => ep_ne_zero hM hw he hz, ep_zero M w he, ?_, fun n => ?_⟩
  · have : ∀ m : ℕ, (0 : ℂ) ^ (e + m * M) = 0 := fun m => zero_pow (by omega)
    simp [lam, this]
  have t1 : ∀ i, Tendsto (fun N => tc (F N) i) atTop (𝓝 (tc (SiegQ.ep M w e) i)) := fun i =>
    (tendsto_iteratedDeriv i h fun N => (hg N).dU).const_mul _
  have t2 : ∀ i, Tendsto (fun N => tc (G N) i) atTop (𝓝 (tc (lam M w e) i)) := fun i =>
    (tendsto_iteratedDeriv i h' hGd).const_mul _
  have cm : ∀ {H : ℂ → ℂ}, Hol H → ∀ i, tc (fun z => -j * H z) i = -j * tc H i := fun {H} hH i =>
    congrFun (HasQ.coeff_unique one_pos (hasQ_tc (hH.const_mul _) one_pos) ((hasQ_tc hH one_pos).const_mul (-j))) i
  have ht : Tendsto (fun N => dc (F N) (fun z => -j * G N z) n) atTop
      (𝓝 (dc (SiegQ.ep M w e) (fun z => -j * lam M w e z) n)) := by
    refine (t1 n).prodMk_nhds ?_
    simp only [tc_mul d1 (d2.const_mul _), fun N => tc_mul (hg N).dU (hg N).dL, conv, cm d2, fun N => cm (hGd N)]
    exact tendsto_finset_sum _ fun p _ => (t1 _).mul ((t2 _).const_mul _)
  have hs : ∀ N, n ≤ N → dc (F N) (fun z => -j * G N z) n = dc (F n) (fun z => -j * G n z) n := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih => rw [e1, e2, dc_mul_lin (hg N).dU (hg N).dL hw _ (by nlinarith), ih]
  rw [tendsto_nhds_unique ht (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop n] with N hN using (hs N hN).symm))]
  exact (hg n).mem n

def Form (M : ℕ) (A : ℤ) (v : ℂ) (f l : ℂ → ℂ) : Prop :=
  ∃ (k i : ℤ) (σ : ℂ) (U L : ℂ → ℂ), (σ = 1 ∨ σ = -1) ∧ (M : ℤ) ∣ k - A * i ∧ IsU M A v U L ∧
    ∀ z, z ≠ 0 → ‖z‖ < 1 → f z = σ * z ^ k * v ^ i * U z ∧ l z = i + L z

theorem Form.congr {f l f' l' : ℂ → ℂ} (h : Form M A v f l)
    (e : ∀ z, z ≠ 0 → ‖z‖ < 1 → f' z = f z ∧ l' z = l z) : Form M A v f' l' := by
  obtain ⟨k, i, σ, U, L, h1, h2, h3, h4⟩ := h
  exact ⟨k, i, σ, U, L, h1, h2, h3, fun z a b => by rw [(e z a b).1, (e z a b).2]; exact h4 z a b⟩

theorem Form.mono {k i : ℤ} {σ : ℂ} (h1 : σ = 1 ∨ σ = -1) (h2 : (M : ℤ) ∣ k - A * i) :
    Form M A v (fun z => σ * z ^ k * v ^ i) (fun _ => i) :=
  ⟨k, i, σ, _, _, h1, h2, IsU.one, fun z _ _ => by simp⟩

theorem IsU.form {U L : ℂ → ℂ} (h : IsU M A v U L) : Form M A v U L :=
  ⟨0, 0, 1, U, L, Or.inl rfl, by simp, h, fun z _ _ => by simp⟩

theorem Form.ne (hv : v ≠ 0) {f l : ℂ → ℂ} (h : Form M A v f l) {z : ℂ} (h0 : z ≠ 0) (hz : ‖z‖ < 1) : f z ≠ 0 := by
  obtain ⟨k, i, σ, U, L, h1, h2, h3, h4⟩ := h
  rw [(h4 z h0 hz).1]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (zpow_ne_zero _ h0)) (zpow_ne_zero _ hv)) (h3.ne z hz)
  rcases h1 with rfl | rfl <;> simp

theorem Form.mul (hv : v ≠ 0) {f l f' l' : ℂ → ℂ} (h : Form M A v f l) (h' : Form M A v f' l') :
    Form M A v (fun z => f z * f' z) (fun z => l z + l' z) := by
  obtain ⟨k, i, σ, U, L, h1, h2, h3, h4⟩ := h
  obtain ⟨k', i', σ', U', L', h1', h2', h3', h4'⟩ := h'
  refine ⟨k + k', i + i', σ * σ', _, _, ?_, ?_, h3.mul hv h3', fun z a b => ?_⟩
  · rcases h1 with rfl | rfl <;> rcases h1' with rfl | rfl <;> simp
  · have := dvd_add h2 h2'
    rwa [show k - A * i + (k' - A * i') = k + k' - A * (i + i') by ring] at this
  · simp only [(h4 z a b).1, (h4 z a b).2, (h4' z a b).1, (h4' z a b).2, zpow_add₀ a, zpow_add₀ hv]
    push_cast
    constructor <;> ring

theorem Form.inv (hv : v ≠ 0) {f l : ℂ → ℂ} (h : Form M A v f l) : Form M A v (fun z => (f z)⁻¹) (fun z => -l z) := by
  obtain ⟨k, i, σ, U, L, h1, h2, h3, h4⟩ := h
  refine ⟨-k, -i, σ, _, _, h1, ?_, h3.inv hv, fun z a b => ?_⟩
  · have := h2.neg_right
    rwa [show -(k - A * i) = -k - A * -i by ring] at this
  · have : σ⁻¹ = σ := by rcases h1 with rfl | rfl <;> simp
    simp only [(h4 z a b).1, (h4 z a b).2, zpow_neg, mul_inv, this]
    push_cast
    exact ⟨trivial, by ring⟩

theorem Form.pow (hv : v ≠ 0) {f l : ℂ → ℂ} (h : Form M A v f l) (n : ℕ) :
    Form M A v (fun z => f z ^ n) (fun z => n * l z) := by
  induction n with
  | zero => simpa using IsU.one.form
  | succ n ih => exact (ih.mul hv h).congr fun z _ _ => ⟨pow_succ _ _, by push_cast; ring⟩

def Th (q t : ℂ) : ℂ := (1 - t) * gP q t * gP q t⁻¹

theorem gP_eq_one_sub_mul_gP {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) : gP q a = (1 - q * a) * gP q (q * a) := by
  have h := hasProd_gP hq (q * a)
  have h1 : HasProd (fun m : ℕ => 1 - q ^ (m + 1 + 1) * a) (gP q (q * a)) :=
    h.congr_fun fun m => by ring
  have := HasProd.prod_range_mul (k := 1) (f := fun m : ℕ => 1 - q ^ (m + 1) * a) h1
  simpa using (hasProd_gP hq a).unique this

theorem gS_step {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) : gS q a = q * a / (1 - q * a) + gS q (q * a) := by
  have sm : Summable (fun m : ℕ => q ^ (m + 1) * a / (1 - q ^ (m + 1) * a)) :=
    ((summable_lambert hq a).mul_right a).congr fun m => by ring
  rw [gS, sm.tsum_eq_zero_add, gS]
  congr 1
  · simp
  · exact tsum_congr fun m => by rw [pow_succ q (m + 1), mul_assoc]

theorem Th_step {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht0 : t ≠ 0) (ht : t ≠ 1) :
    Th q (q * t) = -t⁻¹ * Th q t ∧ E q (q * t) = E q t - 1 := by
  have e : q * (q * t)⁻¹ = t⁻¹ := by field_simp
  have h1 : 1 - t ≠ 0 := sub_ne_zero.2 ht.symm
  have h2 : t - 1 ≠ 0 := sub_ne_zero.2 ht
  constructor
  · rw [Th, Th, gP_eq_one_sub_mul_gP hq t, gP_eq_one_sub_mul_gP hq (q * t)⁻¹, e]
    field_simp
    ring
  · rw [E, E, gS_step hq t, gS_step hq (q * t)⁻¹, e]
    have : t⁻¹ / (1 - t⁻¹) = -(t / (1 - t)) - 1 := by field_simp; ring
    rw [this]; ring

theorem form_base (hM : 0 < M) (hv : ‖v‖ = 1) {j : ℤ} {B : ℕ} (h0 : 0 < B) (hB : B < M) (hd : (M : ℤ) ∣ B - A * j) :
    Form M A v (fun z => Th (z ^ M) (z ^ (B : ℤ) * v ^ j)) (fun z => j * E (z ^ M) (z ^ (B : ℤ) * v ^ j)) := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have h1 := IsU.lin (M := M) (A := A) hv h0 hd
  have h2 := IsU.ep (A := A) hM hv (j := j) (e := M + B) (by omega) (by
    have := dvd_add hd (dvd_refl (M : ℤ))
    rwa [show B - A * j + (M : ℤ) = ((M + B : ℕ) : ℤ) - A * j by push_cast; ring] at this)
  have h3 := IsU.ep (A := A) hM hv (j := -j) (e := M - B) (by omega) (by
    have := dvd_sub (dvd_refl (M : ℤ)) hd
    rwa [show (M : ℤ) - (B - A * j) = ((M - B : ℕ) : ℤ) - A * -j by push_cast [hB.le]; ring] at this)
  refine ((h1.mul hv0 h2).mul hv0 h3).form.congr fun z hz0 hz => ?_
  have e1 : ∀ m : ℕ, (z ^ M) ^ (m + 1) * (z ^ B * v ^ j) = v ^ j * z ^ (M + B + m * M) := fun m => by ring
  have e2 : ∀ m : ℕ, (z ^ M) ^ (m + 1) * (z ^ B * v ^ j)⁻¹ = v ^ (-j) * z ^ (M - B + m * M) := fun m => by
    have h : M * (m + 1) = M - B + m * M + B := by
      have : M - B + B = M := by omega
      nlinarith
    rw [← pow_mul, h, pow_add _ _ B, zpow_neg]
    field_simp
  simp only [zpow_natCast, Th, E, gP, gS, e1, e2, SiegQ.ep, lam]
  rw [mul_comm (z ^ B)]
  push_cast
  exact ⟨rfl, by ring⟩

theorem form_step (hM : 0 < M) (hv : ‖v‖ = 1) {j B : ℤ} (h0 : B ≠ 0) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    Th (z ^ M) (z ^ (B + M) * v ^ j) = -1 * z ^ (-B) * v ^ (-j) * Th (z ^ M) (z ^ B * v ^ j) ∧
      E (z ^ M) (z ^ (B + M) * v ^ j) = E (z ^ M) (z ^ B * v ^ j) - 1 := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hq : ‖z ^ M‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz hM.ne'
  have ht : z ^ B * v ^ j ≠ 1 := fun h => by
    have := congrArg norm h
    rw [norm_mul, norm_zpow, norm_zpow, hv, one_zpow, mul_one, norm_one,
      zpow_eq_one_iff_right₀ (norm_nonneg _) hz.ne] at this
    exact h0 this
  have := Th_step hq (pow_ne_zero _ hz0) (mul_ne_zero (zpow_ne_zero B hz0) (zpow_ne_zero j hv0)) ht
  rw [show z ^ (B + M) * v ^ j = z ^ M * (z ^ B * v ^ j) by rw [zpow_add₀ hz0, zpow_natCast]; ring, this.1, this.2,
    zpow_neg, zpow_neg, mul_inv]
  exact ⟨by ring, rfl⟩

theorem form_Th (hM : 0 < M) (hv : ‖v‖ = 1) {j B : ℤ} (h0 : ¬ (M : ℤ) ∣ B) (hd : (M : ℤ) ∣ B - A * j) :
    Form M A v (fun z => Th (z ^ M) (z ^ B * v ^ j)) (fun z => j * E (z ^ M) (z ^ B * v ^ j)) := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨B0, n, rfl, b1, b2⟩ : ∃ (B0 : ℕ) (n : ℤ), B = B0 + n * M ∧ 0 < B0 ∧ B0 < M := by
    have a1 := Int.emod_nonneg B hMz.ne'
    have a2 := Int.emod_lt_of_pos B hMz
    have a3 : B % M ≠ 0 := fun h => h0 (Int.dvd_of_emod_eq_zero h)
    refine ⟨(B % M).toNat, B / M, ?_, by omega, by omega⟩
    rw [Int.toNat_of_nonneg a1, mul_comm, Int.emod_add_mul_ediv]
  have hd0 : (M : ℤ) ∣ B0 - A * j := by
    have := dvd_sub hd (dvd_mul_left (M : ℤ) n)
    rwa [show B0 + n * (M : ℤ) - A * j - n * M = B0 - A * j by ring] at this
  have hne : ∀ n : ℤ, (B0 : ℤ) + n * M ≠ 0 := fun m h => by
    have : (M : ℤ) ∣ B0 := ⟨-m, by linarith⟩
    have := Int.le_of_dvd (by exact_mod_cast b1) this
    omega
  have hdn : ∀ n : ℤ, (M : ℤ) ∣ B0 + n * M - A * j := fun m => by
    have := dvd_add hd0 (dvd_mul_left (M : ℤ) m)
    rwa [show B0 - A * j + m * (M : ℤ) = B0 + m * M - A * j by ring] at this
  clear h0 hd
  induction n using Int.induction_on with
  | zero => simpa using form_base hM hv b1 b2 hd0
  | succ n ih =>
    refine ((Form.mono (σ := -1) (k := -(B0 + n * M)) (i := -j) (Or.inr rfl) ?_).mul hv0 ih).congr fun z a b => ?_
    · have := (hdn n).neg_right
      rwa [show -(B0 + n * (M : ℤ) - A * j) = -(B0 + n * M) - A * -j by ring] at this
    · have := form_step hM hv (j := j) (hne n) a b
      rw [show (B0 : ℤ) + (n + 1) * M = B0 + n * M + M by ring, this.1, this.2]
      push_cast
      exact ⟨rfl, by ring⟩
  | pred n ih =>
    refine ((Form.mono (σ := -1) (k := B0 + (-n - 1) * M) (i := j) (Or.inr rfl) (hdn _)).mul hv0 ih).congr
      fun z a b => ?_
    have := form_step hM hv (j := j) (hne (-n - 1)) a b
    rw [show (B0 : ℤ) + (-n - 1) * M + M = B0 + -n * M by ring] at this
    rw [this.1, this.2, zpow_neg, zpow_neg]
    have := zpow_ne_zero (B0 + (-n - 1) * (M : ℤ)) a
    have := zpow_ne_zero j hv0
    exact ⟨by field_simp, by ring⟩

theorem form_cth (hM : 0 < M) (hv : ‖v‖ = 1) {c : ℕ} (h1 : ¬ (M : ℤ) ∣ A) (h2 : ¬ (M : ℤ) ∣ A * c) :
    Form M A v (fun z => cth c (z ^ M) (z ^ A * v))
      (fun z => (kk c : ℂ) + c ^ 2 * E (z ^ M) (z ^ A * v) - c * E (z ^ M) ((z ^ A * v) ^ c)) := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have a := form_Th (A := A) hM hv (j := 1) h1 (by simp)
  have b := form_Th (A := A) hM hv (j := c) h2 (by simp)
  have m := Form.mono (M := M) (A := A) (v := v) (σ := (-1) ^ kk c)
    (k := (M * ((c ^ 2 - 1) / 12) : ℕ) + A * kk c) (i := kk c)
    (by rcases Int.even_or_odd (kk c) with h | h
        · exact Or.inl h.neg_one_zpow
        · exact Or.inr h.neg_one_zpow) (by simp)
  refine ((m.mul hv0 (a.pow hv0 (c ^ 2))).mul hv0 (b.inv hv0)).congr fun z hz0 hz => ?_
  have hq : ‖z ^ M‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz hM.ne'
  have e : z ^ (A * c) * v ^ (c : ℤ) = (z ^ A * v) ^ c := by rw [zpow_mul, zpow_natCast, zpow_natCast, mul_pow]
  have hb := b.ne hv0 hz0 hz
  simp only [e, Th, mul_assoc] at hb
  simp only [e, zpow_one]
  constructor
  · rw [cth, tprod_cthFac_eq hq c (right_ne_zero_of_mul hb), ← kk, zpow_add₀ hz0, zpow_natCast, pow_mul, zpow_mul,
      neg_eq_neg_one_mul (z ^ A * v), mul_zpow, mul_zpow, Th, Th]
    simp only [div_eq_mul_inv, mul_inv, mul_pow]
    ring
  · push_cast; ring

theorem sg_jets {c : ℕ} {b : ℤ} (hM : 0 < M) (hadm : admitted c ![(A : ℚ) / M, (b : ℚ) / M]) (h1 : ¬ (M : ℤ) ∣ A)
    (h2 : ¬ (M : ℤ) ∣ A * c) :
    ∃ (k : ℤ) (a g : ℕ → ℂ),
      HasQ M (fun τ => sg c ![(A : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) a ∧
      HasQ M (fun τ => -cF c 1 ![(A : ℚ) / M, (b : ℚ) / M] τ *
        (sg c ![(A : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ)))) g ∧
      (∀ n : ℕ, (a n, g n) ∈ jets M A (ee ((b : ℂ) / M)) (k + n)) ∧
      ∃ i : ℤ, a 0 = ee ((b : ℂ) / M) ^ i ∨ a 0 = -ee ((b : ℂ) / M) ^ i := by
  set v := ee ((b : ℂ) / M) with hvd
  set x : Fin 2 → ℚ := ![(A : ℚ) / M, (b : ℚ) / M] with hxd
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hv : ‖v‖ = 1 := by
    rw [hvd, norm_ee, show (b : ℂ) / M = ((b / M : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]; simp
  have hv0 : v ≠ 0 := ee_ne_zero _
  obtain ⟨k, i, σ, U, L, s1, s2, s3, s4⟩ := form_cth hM hv h1 h2
  have key : ∀ τ : ℍ, sg c x τ * ee (-((k : ℂ) / M) * (τ : ℂ)) = σ * v ^ i * U (qv M τ) ∧
      -cF c 1 x τ = i + L (qv M τ) := by
    intro τ
    have hz0 : qv M τ ≠ 0 := Complex.exp_ne_zero _
    have e1 : ee τ = qv M τ ^ M := by
      rw [ee, qv, ← Complex.exp_nat_mul]; congr 1; field_simp
    have e2 : ee (pt x τ) = qv M τ ^ A * v := by
      rw [hvd, ee, ee, qv, ← Complex.exp_int_mul, ← Complex.exp_add]
      congr 1
      simp only [pt, hxd, Matrix.cons_val_one, Matrix.cons_val_zero]
      push_cast
      ring
    have e3 : ee (-((k : ℂ) / M) * (τ : ℂ)) = qv M τ ^ (-k) := by
      rw [ee, qv, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    obtain ⟨t1, t2⟩ := s4 _ hz0 (norm_qv_lt hM τ)
    beta_reduce at t1 t2
    constructor
    · rw [sg, e1, e2, e3, t1, zpow_neg]
      have := zpow_ne_zero k hz0
      field_simp
    · rw [← t2, ← e2, ← e1]
      have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
        simpa using hadm.2.2
      have hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
        rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exact hadm.2.2 ⟨⟨c * a, by rw [← ha]; push_cast; ring⟩, ⟨c * b, by rw [← hb]; push_cast; ring⟩⟩
      rw [ee_pt_pow, E_eq hx, E_eq hc, cF]
      have e : (2 : ℂ) * ((kk c : ℤ) : ℂ) = (c : ℂ) - (c : ℂ) ^ 2 := by
        unfold kk
        exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (exponent_exact hadm.2.1).2
      have e2 : (((c • x) 0 : ℚ) : ℂ) = c * (x 0 : ℂ) := by simp
      have e3 : (c : ℂ) ^ (2 - ((1 : ℕ) : ℤ)) = c := by norm_num
      rw [e2, e3]
      linear_combination (-1 / 2 : ℂ) * e
  have q1 := hasQ_tc s3.dU hM
  have q2 := hasQ_tc (s3.dU.fun_mul s3.dL) hM
  refine ⟨k, fun n => σ * v ^ i * tc U n, fun n => σ * v ^ i * tc (fun z => U z * L z) n + σ * (i * v ^ i) * tc U n,
    ?_, ?_, fun n => ?_, i, ?_⟩
  · simp only [fun τ => (key τ).1]
    exact q1.const_mul _
  · have := (q2.const_mul (σ * v ^ i)).add (q1.const_mul (σ * (i * v ^ i)))
    convert this using 2 with τ
    rw [(key τ).1, (key τ).2]
    ring
  · have g : (σ * v ^ i, σ * (i * v ^ i)) ∈ jets M A v k := by
      rcases s1 with rfl | rfl
      · simpa using gen_mem s2
      · simpa using neg_mem (gen_mem (v := v) s2)
    exact dm_mem hv0 g (s3.mem n)
  · rcases s1 with rfl | rfl <;> simp [tc_zero, s3.U0]

open GlobalTheory.KZ in

theorem exp_of_hasQ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) (f : T.K) (g : ℍ → ℂ) {M : ℕ}
    (hM : 0 < M) (k : ℤ) (A' : ℕ → ℂ)
    (hmem : T.an f = ((fun z => g (UpperHalfPlane.ofComplex z) : ℂ → ℂ) : Mero))
    (hA' : HasQ M (fun τ => g τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A') :
    (∀ n : ℕ, ε ((T.exp f).coeff (((k : ℚ) + n) / M)) = A' n) ∧
      ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → (T.exp f).coeff r = 0 := by
  classical
  obtain ⟨φ, C, hφ, hsum⟩ := T.an_exp f
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let ι : ℕ → ℚ := fun n => ((k : ℚ) + n) / M
  have hι : Function.Injective ι := by
    intro n m h
    simp only [ι] at h
    rw [div_left_inj' hMq, add_right_inj] at h
    exact_mod_cast h
  let B : ℚ → ℂ := fun r => if h : ∃ n, ι n = r then A' h.choose else 0
  have hBι : ∀ n, B (ι n) = A' n := by
    intro n
    have h : ∃ m, ι m = ι n := ⟨n, rfl⟩
    simp only [B, dif_pos h]
    rw [hι h.choose_spec]
  have hB0 : ∀ r, r ∉ Set.range ι → B r = 0 := by
    intro r hr
    simp only [B]
    rw [dif_neg]
    exact hr
  have hBsum : ∀ z : ℂ, 0 < z.im →
      HasSum (fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (g (UpperHalfPlane.ofComplex z)) := by
    intro z hz
    have h2 := (hA' ⟨z, hz⟩).mul_left (ee ((k : ℂ) / M * z))
    rw [← hι.hasSum_iff (fun r hr => by simp [hB0 r hr])]
    have e1 : ((fun r : ℚ => B r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) ∘ ι) = fun n : ℕ =>
        ee ((k : ℂ) / M * z) * (A' n * Complex.exp (2 * Real.pi * Complex.I * n * z / M)) := by
      funext n
      simp only [Function.comp_apply, hBι, ι, ee]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
    have e2 : g (UpperHalfPlane.ofComplex z) = ee ((k : ℂ) / M * z) * (g ⟨z, hz⟩ * ee (-((k : ℂ) / M) * z)) := by
      simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rw [mul_left_comm, ee, ee, ← Complex.exp_add]
      have : 2 * Real.pi * Complex.I * ((k : ℂ) / M * z) + 2 * Real.pi * Complex.I * (-((k : ℂ) / M) * (z : ℂ)) = 0 := by
        ring
      rw [this, Complex.exp_zero, mul_one]
    rw [e1, e2]
    simpa using h2
  have hgerm : φ =ᶠ[Filter.codiscreteWithin Hs] fun z => g (UpperHalfPlane.ofComplex z) := by
    have := hφ.symm.trans hmem
    exact Filter.Germ.coe_eq.mp this
  let S : Set ℂ := {z | C < z.im ∧ 0 < z.im ∧ φ z = g (UpperHalfPlane.ofComplex z)}
  have hS : ∀ y : ℝ, ∃ z ∈ S, y < z.im := by
    intro y
    set Y := max (max y C) 0 + 1 with hY
    set w : ℂ := Complex.I * Y
    have hwim : w.im = Y := by simp [w]
    have hw : w ∈ Hs := by
      show 0 < w.im
      rw [hwim]; have := le_max_right (max y C) 0; linarith
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hgerm w hw
    have h2 : Metric.ball w (1 / 2) ∈ nhdsWithin w {w}ᶜ :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by norm_num))
    obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
    have hdist : |z.im - Y| < 1 / 2 := by
      have := Complex.abs_im_le_norm (z - w)
      rw [Metric.mem_ball, dist_eq_norm] at hz2
      rw [Complex.sub_im, hwim] at this
      linarith
    have hyY : y ≤ max (max y C) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hCY : C ≤ max (max y C) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
    have h0Y : 0 ≤ max (max y C) 0 := le_max_right _ _
    have hzim : max (max y C) 0 + 1 / 2 < z.im := by
      have := (abs_lt.mp hdist).1; linarith
    have hzH : z ∈ Hs := show 0 < z.im by linarith
    refine ⟨z, ⟨by linarith, by linarith, ?_⟩, by linarith⟩
    rcases hz1 with h | h
    · exact h
    · exact absurd hzH h
  let d : ℚ → ℂ := fun r => ε ((T.exp f).coeff r) - B r
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ S ?_ (Complex.I * (|C| + 1)) ?_ hS
    · have hR : (Set.range ι).IsWF := by
        have : Set.range ι = ι '' Set.univ := Set.image_univ.symm
        rw [this]
        refine (Set.IsPWO.image_of_monotone (Set.isPWO_of_wellQuasiOrderedLE _) ?_).isWF
        intro n m h
        simp only [ι]
        gcongr
      refine ((T.exp f).isWF_support.union hR).mono ?_
      · intro r hr
        by_contra hn
        simp only [Set.mem_union, not_or] at hn
        apply hr
        simp only [d, hB0 r hn.2]
        have : (T.exp f).coeff r = 0 := by simpa [HahnSeries.support] using hn.1
        simp [this]
    · intro z hz
      have := (hsum z hz.1).sub (hBsum z hz.2.1)
      rw [hz.2.2, sub_self] at this
      simpa [d, sub_mul] using this
    · have hzi : C < (Complex.I * (|C| + 1)).im := by
        simp; have := le_abs_self C; linarith
      have hzp : 0 < (Complex.I * (|C| + 1)).im := by simp; positivity
      have := ((hsum _ hzi).summable.sub (hBsum _ hzp).summable)
      simpa [d, sub_mul] using this
  have hdr : ∀ r, ε ((T.exp f).coeff r) = B r := fun r => sub_eq_zero.mp (congrFun hd r)
  refine ⟨fun n => by rw [hdr]; exact hBι n, fun r hr => ?_⟩
  have hr' : r ∉ Set.range ι := by
    rintro ⟨n, rfl⟩
    exact hr n rfl
  have := hdr r
  rw [hB0 r hr'] at this
  exact (map_eq_zero_iff ε ε.injective).mp this

end GlobalTheory.SiegTwo
