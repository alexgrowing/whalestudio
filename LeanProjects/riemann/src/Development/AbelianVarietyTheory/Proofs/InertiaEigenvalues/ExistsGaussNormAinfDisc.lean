import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.DiscGauss

theorem le_gauge (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (N : A → ℝ)
    (rank_lt_alt : ∀ x, 0 ≤ N x ∧ N x ≤ 1) (Nadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (Nneg : ∀ x, N (-x) = N x)
    (Nmul : ∀ x y, N (x * y) = N x * N y) (Nl : N (l : A) = (l : ℝ)⁻¹) (Nu : N u ≤ ρ) (x : A) :
    N x ≤ ‖toDisc l u ρ x‖ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have N1 : N 1 = 1 := by
    have := Nmul l 1
    rw [mul_one, Nl] at this
    exact (mul_left_cancel₀ (inv_pos.2 hl0).ne' (by rw [mul_one]; exact this)).symm
  have Npow : ∀ (x : A) (k : ℕ), N (x ^ k) = N x ^ k := by
    intro x k
    induction k with
    | zero => simpa using N1
    | succ k ih => rw [pow_succ, Nmul, ih, pow_succ]
  obtain ⟨M, M0, Madd, -, Mmul, MN⟩ := GlobalTheory.GaussExt.exists_ext_loc (S := PreDisc l u ρ)
    (Submonoid.powers (l : A)) N (fun x => (rank_lt_alt x).1) Nadd Nneg Nmul (by
      rintro _ ⟨k, rfl⟩
      dsimp only
      rw [Npow, Nl]
      exact pow_ne_zero _ (inv_pos.2 hl0).ne')
  have M1 : M 1 = 1 := by rw [← map_one (algebraMap A (PreDisc l u ρ)), MN, N1]
  have Mpow : ∀ (x : PreDisc l u ρ) (k : ℕ), M (x ^ k) = M x ^ k := by
    intro x k
    induction k with
    | zero => simpa using M1
    | succ k ih => rw [pow_succ, Mmul, ih, pow_succ]
  have Minv : M (IsLocalization.Away.invSelf (l : A)) = l := by
    have h := congrArg M (IsLocalization.Away.mul_invSelf (S := PreDisc l u ρ) (l : A))
    rw [Mmul, MN, Nl, M1, inv_mul_eq_one₀ hl0.ne'] at h
    exact h.symm
  have Mz : M 0 = 0 := by
    have h := Mmul (IsLocalization.Away.invSelf (l : A)) 0
    rw [mul_zero, Minv] at h
    have := M0 0
    nlinarith
  have key : ∀ r : ℝ, 0 < r → ∀ y ∈ ball l u ρ r, M y ≤ r := by
    intro r hr y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, b, c, h1, rfl⟩ := hy
      rw [Mmul, MN, Nmul, Npow, Npow, Mpow, Minv, Nl]
      have h2 : N u ^ b ≤ (ρ : ℝ) ^ b := pow_le_pow_left₀ (rank_lt_alt u).1 Nu b
      calc (l : ℝ)⁻¹ ^ a * N u ^ b * (l : ℝ) ^ c ≤ (l : ℝ)⁻¹ ^ a * (ρ : ℝ) ^ b * (l : ℝ) ^ c := by gcongr
        _ = ((l : ℝ) ^ c * (ρ : ℝ) ^ b) / (l : ℝ) ^ a := by rw [inv_pow]; field_simp
        _ ≤ r := by rwa [div_le_iff₀ (by positivity)]
    | zero => rw [Mz]; exact hr.le
    | add x y _ _ hx hy => exact (Madd x y).trans (max_le hx hy)
    | smul a x _ hx =>
      rw [Algebra.smul_def, Mmul, MN]
      exact (mul_le_mul (rank_lt_alt a).2 hx (M0 x) zero_le_one).trans (one_mul r).le
  rw [← MN x]
  change _ ≤ ‖ofPre l u ρ (algebraMap A _ x)‖
  rw [norm_ofPre]
  exact le_of_forall_gt_imp_ge_of_dense fun r hr =>
    key r ((gauge_nonneg l u ρ _).trans_lt hr) _ (mem_ball_of_gauge_lt l u ρ hr)

theorem exists_pow_btwn {ρ s t : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (hs : 0 < s) (ht : t ≤ 1) (h : t < ρ * s) :
    ∃ b : ℕ, t ≤ ρ ^ b ∧ ρ ^ b ≤ s := by
  classical
  have hex : ∃ b : ℕ, ρ ^ b ≤ s := (exists_pow_lt_of_lt_one hs h1).imp fun _ h => h.le
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hb : Nat.find hex with _ | b
  · simpa using ht
  · have h2 := Nat.find_min hex (m := b) (by omega)
    rw [not_le] at h2
    rw [pow_succ']
    exact (h.trans (mul_lt_mul_of_pos_left h2 h0)).le

theorem root_pow (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] [CharP R l] [PerfectRing R l] (i : ℕ) (w : R) :
    ((_root_.frobeniusEquiv R l).symm ^ i) w ^ l ^ i = w := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', RingAut.mul_apply, pow_succ', pow_mul, ← frobenius_def l ((_root_.frobeniusEquiv R l).symm _),
      frobenius_apply_frobeniusEquiv_symm, ih]

theorem exists_gauss (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ)
    (a01 : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (a0 : a 0 = 0) (a1 : a 1 = 1) (amul : ∀ x y, a (x * y) = a x * a y)
    (aadd : ∀ x y, a (x + y) ≤ max (a x) (a y)) (advd : ∀ x y, a x ≤ a y → y ∣ x) (f : R) (ρ : ℝ≥0)
    (h0 : 0 < ρ) (h1 : ρ < 1) (hf : a f = ρ) :
    ∃ N : WittVector l R → ℝ, (∀ x y, N (x * y) = N x * N y) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧
      N (l : WittVector l R) = (l : ℝ)⁻¹ ∧ (∀ x, N x ≤ ‖toDisc l (WittVector.teichmuller l f) ρ x‖) ∧
      ∀ x, (ρ : ℝ) * ‖toDisc l (WittVector.teichmuller l f) ρ x‖ ≤ N x := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have h0' : (0 : ℝ) < ρ := h0
  have h1' : (ρ : ℝ) < 1 := h1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (l : ℝ)⁻¹ := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ inv_pos.2 hl0
  have hr1 : r < 1 := hr ▸ inv_lt_one_of_one_lt₀ hl1
  have apow : ∀ (x : R) (k : ℕ), a (x ^ k) = a x ^ k := by
    intro x k
    induction k with
    | zero => simpa using a1
    | succ k ih => rw [pow_succ, amul, ih, pow_succ]
  obtain ⟨N, hN⟩ : ∃ N : WittVector l R → ℝ,
      ∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := ⟨_, fun _ => rfl⟩
  obtain ⟨Nadd, Nneg, -⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l R a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have Nmul := GlobalTheory.T.wittVector_gaussNorm_mul l R a a01 a0 a1 amul aadd r hr0 hr1 N hN
  have he : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have ht0 : ∀ (y : R) (n : ℕ), 0 ≤ a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := fun y n =>
    mul_nonneg (Real.rpow_nonneg (a01 y).1 _) (pow_nonneg hr0.le _)
  have ht1 : ∀ (y : R) (n : ℕ), a y ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ r ^ n := fun y n =>
    mul_le_of_le_one_left (pow_nonneg hr0.le _) (Real.rpow_le_one (a01 y).1 (a01 y).2 (he n).le)
  have rank_lt_alt : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := fun x => by
    rw [hN]
    exact ⟨Real.iSup_nonneg fun n => ht0 _ n,
      ciSup_le fun n => (ht1 _ n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have Nge : ∀ x (n : ℕ), a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ N x := fun x n => by
    rw [hN]
    refine le_ciSup (f := fun n : ℕ => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) ⟨1, ?_⟩ n
    rintro _ ⟨n, rfl⟩
    exact (ht1 _ n).trans (pow_le_one₀ hr0.le hr1.le)
  have Nl : N (l : WittVector l R) = r := by
    refine le_antisymm ?_ (by simpa [WittVector.coeff_p, a1] using Nge l 1)
    rw [hN]
    refine ciSup_le fun n => ?_
    rw [WittVector.coeff_p]
    split_ifs with h
    · rw [a1, h, Real.one_rpow, one_mul, pow_one]
    · rw [a0, Real.zero_rpow (he n).ne', zero_mul]; exact hr0.le
  have Nu : N (WittVector.teichmuller l f) ≤ ρ := by
    rw [hN]
    refine ciSup_le fun n => ?_
    rcases n with _ | n
    · simp [hf]
    · rw [WittVector.teichmuller_coeff_pos l f _ n.succ_pos, a0, Real.zero_rpow (he _).ne', zero_mul]
      exact h0'.le
  refine ⟨N, Nmul, Nadd, Nl.trans hr, le_gauge l _ ρ N rank_lt_alt Nadd Nneg Nmul (Nl.trans hr) Nu, fun x => ?_⟩
  rw [← le_div_iff₀' h0']
  refine le_of_forall_gt_imp_ge_of_dense fun s hs => ?_
  have hs0 : 0 < s := (div_nonneg (rank_lt_alt x).1 h0'.le).trans_lt hs
  rw [div_lt_iff₀' h0'] at hs
  change ‖ofPre l _ ρ (algebraMap _ _ x)‖ ≤ _
  rw [norm_ofPre]
  refine gauge_le l _ ρ hs0 ?_
  have mono : ∀ (i b : ℕ) (z : WittVector l R), (ρ : ℝ) ^ b ≤ s * (l : ℝ) ^ i →
      algebraMap _ (PreDisc l (WittVector.teichmuller l f) ρ)
        (z * ((l : WittVector l R) ^ i * WittVector.teichmuller l f ^ b)) ∈
        ball l (WittVector.teichmuller l f) ρ s := by
    intro i b z h
    rw [map_mul, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, b, 0, by simpa using h, by simp⟩)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt s⁻¹ hl1
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_sum]
  refine add_mem ?_ (Submodule.sum_mem _ fun i _ => ?_)
  · have := mono (n + 1) 0 c (by
      have h2 : (l : ℝ) ^ n ≤ (l : ℝ) ^ (n + 1) := pow_le_pow_right₀ hl1.le n.le_succ
      rw [pow_zero, ← inv_mul_le_iff₀ hs0, mul_one]
      exact hn.le.trans h2)
    rwa [pow_zero, mul_one, mul_comm] at this
  · set y := ((_root_.frobeniusEquiv R l).symm ^ i) (x.coeff i) with hy
    have hy2 : y ^ l ^ i = x.coeff i := root_pow l i _
    have hy3 : a y * r ^ i ≤ N x := by
      have h := Nge x i
      rw [← hy2, apow, one_div, ← Nat.cast_pow,
        Real.pow_rpow_inv_natCast (a01 y).1 (pow_ne_zero _ hl.out.ne_zero)] at h
      exact h
    obtain ⟨b, hb1, hb2⟩ := exists_pow_btwn h0' h1' (s := s * (l : ℝ) ^ i) (by positivity) (a01 y).2 (by
      have h := hy3.trans_lt hs
      rwa [hr, inv_pow, ← div_eq_mul_inv, div_lt_iff₀ (by positivity), mul_assoc] at h)
    obtain ⟨z, hz⟩ := advd y (f ^ b) (by rwa [apow, hf])
    have := mono i b (WittVector.teichmuller l z) hb2
    convert this using 2
    rw [hz, map_mul, map_pow]; ring

theorem dvd_of_norm_le {l : ℕ} [Fact l.Prime] (x y : Per.Fl l)
    (h : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ≤ ‖((y.untilt : Per.OC l) : ℂ_[l])‖) : y ∣ x := by
  refine GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd ?_
  by_cases hy : ((y.untilt : Per.OC l) : ℂ_[l]) = 0
  · rw [hy, norm_zero, norm_le_zero_iff] at h
    rw [show x.untilt = 0 from Subtype.ext h]
    exact dvd_zero _
  · refine ⟨⟨(x.untilt : Per.OC l) / (y.untilt : Per.OC l), (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rwa [norm_div, div_le_one (norm_pos_iff.2 hy)]
    · push_cast
      exact (mul_div_cancel₀ _ hy).symm

theorem exists_gauss_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ N : Ainf l → ℝ, (∀ x y, N (x * y) = N x * N y) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ N (l : Ainf l) = (l : ℝ)⁻¹ ∧ (∀ x, N x ≤ ‖toDisc l (bk.ev X) ρ x‖) ∧ ∀ x, (ρ : ℝ) * ‖toDisc l (bk.ev X) ρ x‖ ≤ N x := by
  intro l _ K bk ρ h0 h1
  obtain ⟨hf0, hfu, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have h0' : (0 : ℝ) < ρ := h0
  have h1' : (ρ : ℝ) < 1 := h1
  let v : Per.Fl l → ℝ := fun x => ‖((x.untilt : Per.OC l) : ℂ_[l])‖
  have v01 : ∀ x, 0 ≤ v x ∧ v x ≤ 1 := fun x => ⟨norm_nonneg _, (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2⟩
  have v0 : v 0 = 0 := by simp only [v, GlobalTheory.GaussExt.untilt_zero]; simp
  have v1 : v 1 = 1 := by simp [v]
  have vmul : ∀ x y, v (x * y) = v x * v y := by intro x y; simp [v]
  have vadd : ∀ x y, v (x + y) ≤ max (v x) (v y) := fun x y => (GlobalTheory.T.untilt_norm_ultrametric_eq_zero l x y).1
  have vdvd : ∀ x y, v x ≤ v y → y ∣ x := dvd_of_norm_le
  have vf0 : 0 < v bk.flat := norm_pos_iff.2 fun h => hf0 ((GlobalTheory.T.untilt_norm_ultrametric_eq_zero l bk.flat 0).2 (Subtype.ext h))
  have vf1 : v bk.flat < 1 := lt_of_not_ge fun h => hfu (isUnit_of_dvd_one (vdvd 1 _ (v1 ▸ h)))
  obtain ⟨t, ht, hρ⟩ : ∃ t : ℝ, 0 < t ∧ v bk.flat ^ t = ρ :=
    ⟨Real.logb (v bk.flat) ρ, Real.logb_pos_of_base_lt_one vf0 vf1 h0' h1', Real.rpow_logb vf0 vf1.ne h0'⟩
  rw [bk.ev_X]
  exact exists_gauss l (Per.Fl l) (fun x => v x ^ t)
    (fun x => ⟨Real.rpow_nonneg (v01 x).1 _, Real.rpow_le_one (v01 x).1 (v01 x).2 ht.le⟩)
    (by simp only [v0]; exact Real.zero_rpow ht.ne') (by simp only [v1]; exact Real.one_rpow t)
    (fun x y => by simp only [vmul]; exact Real.mul_rpow (v01 x).1 (v01 y).1)
    (fun x y => by
      rcases le_max_iff.1 (vadd x y) with h | h
      · exact le_max_of_le_left (Real.rpow_le_rpow (v01 _).1 h ht.le)
      · exact le_max_of_le_right (Real.rpow_le_rpow (v01 _).1 h ht.le))
    (fun x y h => vdvd x y ((Real.rpow_le_rpow_iff (v01 x).1 (v01 y).1 ht).1 h)) bk.flat ρ h0 h1 hρ

end GlobalTheory.DiscGauss
