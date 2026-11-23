import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfA
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DomSubsetClosureIsGenFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.Low

open MvPolynomial Filter

section Alg

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem eval₂_smul_of_isHomogeneous {ι : Type} {F : MvPolynomial ι K} {e : ℕ} (hF : F.IsHomogeneous e)
    (x : ι → ℂ) (c : ℂ) : eval₂ σ (fun j => c * x j) F = c ^ e * eval₂ σ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = e := by
    have := hF (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem eval₂_cons_zero {n : ℕ} (y : Fin n → ℂ) (Q : MvPolynomial (Fin (n + 1)) K) :
    eval₂ σ (Fin.cons 0 y : Fin (n + 1) → ℂ) Q = eval₂ σ y ((finSuccEquiv K n Q).coeff 0) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have : finSuccEquiv K n (C a) = Polynomial.C (C a) := by simp [finSuccEquiv_apply]
    simp [this]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, eval₂_mul, eval₂_mul, hp]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

theorem exists_rel_coeff_zero_ne {Y : Type} {n : ℕ} (S : Set Y) (u : Fin (n + 1) → Y → ℂ)
    (hu : ∀ x ∈ S, u 0 x ≠ 0) (d : ℕ) : ∀ Q : MvPolynomial (Fin (n + 1)) K, Q ≠ 0 → Q.IsHomogeneous d →
      (∀ x ∈ S, eval₂ σ (fun i => u i x) Q = 0) →
      ∃ (Q' : MvPolynomial (Fin (n + 1)) K) (d' : ℕ), (finSuccEquiv K n Q').coeff 0 ≠ 0 ∧ Q'.IsHomogeneous d' ∧
        ∀ x ∈ S, eval₂ σ (fun i => u i x) Q' = 0 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro Q hQ hh hv
    by_cases h0 : (finSuccEquiv K n Q).coeff 0 = 0
    · obtain ⟨p, hp⟩ := Polynomial.X_dvd_iff.mpr h0
      set Q1 := (finSuccEquiv K n).symm p with hQ1
      have hQQ : Q = MvPolynomial.X 0 * Q1 := by
        apply (finSuccEquiv K n).injective
        rw [map_mul, finSuccEquiv_X_zero, hQ1, AlgEquiv.apply_symm_apply, hp]
      have hQ1ne : Q1 ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hQQ
        exact hQ hQQ
      have key : ∀ m, Q1.coeff m ≠ 0 → Finsupp.weight (1 : Fin (n + 1) → ℕ) m + 1 = d := by
        intro m hm
        have h1 : Q.coeff (Finsupp.single 0 1 + m) ≠ 0 := by
          rw [hQQ, coeff_X_mul]; exact hm
        have := hh h1
        rw [map_add, Finsupp.weight_single] at this
        simp at this
        omega
      obtain ⟨m, hm⟩ := ne_zero_iff.mp hQ1ne
      have hd := key m hm
      refine ih (d - 1) (by omega) Q1 hQ1ne (fun m' hm' => ?_) (fun x hx => ?_)
      · have := key m' hm'
        omega
      · have := hv x hx
        rw [hQQ, eval₂_mul, eval₂_X] at this
        exact (mul_eq_zero.mp this).resolve_left (hu x hx)
    · exact ⟨Q, d, h0, hh, hv⟩

theorem continuous_eval₂ {ι : Type} (Q : MvPolynomial ι K) : Continuous fun y : ι → ℂ => eval₂ σ y Q := by
  have := MvPolynomial.continuous_eval (MvPolynomial.map σ Q)
  simpa only [eval_map] using this

theorem isHomogeneous_expand {ι : Type} {F : MvPolynomial ι K} {e : ℕ} (hF : F.IsHomogeneous e) (k : ℕ) :
    (expand k F).IsHomogeneous (k * e) := by
  have := hF.aeval (fun i => (MvPolynomial.X i : MvPolynomial ι K) ^ k) (n := k) (fun i => by
    simpa using (isHomogeneous_X K i).pow k)
  exact this

theorem eval₂_expand' {ι : Type} (F : MvPolynomial ι K) (k : ℕ) (y : ι → ℂ) :
    eval₂ σ y (expand k F) = eval₂ σ (fun i => y i ^ k) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Alg

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (Xa : ArchInM X)

theorem decay_le : ∃ C : ℝ, ∀ x ∈ X.dom, ‖Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2))‖ ^ 2 ≤
    C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) * (‖fun j => Xa.w j x‖ ^ (2 * (Xa.i * (Xa.g0 / 2)))) ^ 2 := by
  obtain ⟨K3, h3⟩ := Xa.p3
  obtain ⟨K4, h4⟩ := Xa.p4
  obtain ⟨B, hB⟩ := Xa.firstTheta_vanishes.1.1.2
  set n1 := Xa.i * (Xa.g0 / 2) with hn1
  refine ⟨|K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * (Xa.N : ℝ) ^ (2 * n1), fun x hx => ?_⟩
  set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hW
  set ρ := ‖fun j => Xa.w j x‖ with hρ
  set e := Real.exp (-phla X Xa.L x) with he
  have he0 : 0 < e := Real.exp_pos _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hWle : W ≤ Xa.N * ρ ^ 2 * e := by
    rw [hW, OW.sum_pnorm_sq X _ _ hx]
    refine mul_le_mul_of_nonneg_right ?_ he0.le
    calc ∑ k, Complex.normSq (Xa.w k x) ≤ ∑ _k : Fin Xa.N, ρ ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← Complex.sq_norm]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (fun j => Xa.w j x) k) 2
      _ = Xa.N * ρ ^ 2 := by simp
  have hph : phla X (n1 • Xa.de) x + n1 * phla X (2 • Xa.L - Xa.de) x = ((2 * n1 : ℕ) : ℝ) * phla X Xa.L x := by
    have h0 : phla X 0 x = 0 := by rw [IW.phla_eq X hx]; simp
    rw [← OW.phla_add_nsmul X hx]
    have : n1 • Xa.de + n1 • (2 • Xa.L - Xa.de) = 0 + (2 * n1) • Xa.L := by
      rw [smul_sub, ← mul_smul, mul_comm]; abel
    rw [this, OW.phla_add_nsmul X hx, h0, zero_add]
  have hid : ‖Xa.et x * Xa.th1 x ^ n1‖ ^ 2 * e ^ (2 * n1) =
      X.pnorm (n1 • Xa.de) Xa.et x ^ 2 * (X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2) ^ n1 := by
    rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, he, ← Real.exp_nat_mul, mul_neg, ← hph, neg_add, Real.exp_add,
      ← mul_neg, Real.exp_nat_mul, ← Complex.sq_norm, ← Complex.sq_norm, norm_mul, norm_pow]
    ring
  have hpt : X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2
  have hk : ((2 * n1 : ℕ) : ℝ) = Xa.i * Xa.g0 := by
    obtain ⟨m, hm⟩ := Xa.genus_even
    have : 2 * n1 = Xa.i * Xa.g0 := by
      rw [hn1, hm, ← two_mul, Nat.mul_div_cancel_left _ two_pos]; ring
    rw [this]; push_cast; rfl
  have hexp : Real.exp (-(2 * Xa.i * Xa.ph x)) ≤ Real.exp (-(2 * Xa.c * Xa.ph x)) ^ (2 * n1 + 1) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp, Nat.cast_add, hk]
    have hT : (2 : ℝ) ≤ Xa.T := by
      have h1 := Xa.T_ge
      have h2 := Xa.n_ge
      have : 2 ≤ Xa.T := by nlinarith
      exact_mod_cast this
    have hi : (1 : ℝ) ≤ Xa.i := by exact_mod_cast Xa.i_pos
    have hg : (1 : ℝ) ≤ Xa.g0 := by exact_mod_cast Xa.genus_pos
    have hc := Xa.c_pos
    have hT' := Xa.Tcg0
    have hφ := Xa.ph_nonneg x hx
    have a1 : Xa.c * Xa.g0 ≤ 1 / 2 := by nlinarith [mul_pos hc (lt_of_lt_of_le one_pos hg)]
    have a2 : Xa.c ≤ 1 / 2 := by nlinarith
    have a3 : (Xa.i * Xa.g0 + 1) * Xa.c ≤ Xa.i := by nlinarith
    have := mul_le_mul_of_nonneg_right a3 hφ
    push_cast
    nlinarith
  have hg : Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ |K3| * W :=
    (h3 x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hW0)
  have hpe : X.pnorm (n1 • Xa.de) Xa.et x ^ 2 ≤ |K4| * (|K3| * W) ^ (2 * n1 + 1) :=
    (h4 x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (hexp.trans (pow_le_pow_left₀ (Real.exp_pos _).le hg _)) (abs_nonneg _)))
  refine le_of_mul_le_mul_right ?_ (pow_pos he0 (2 * n1))
  rw [hid]
  calc _ ≤ (|K4| * (|K3| * W) ^ (2 * n1 + 1)) * (B ^ 2) ^ n1 :=
        mul_le_mul hpe (pow_le_pow_left₀ (sq_nonneg _) hpt _) (by positivity) (by positivity)
    _ = |K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * W * W ^ (2 * n1) := by ring
    _ ≤ |K4| * (B ^ 2) ^ n1 * |K3| ^ (2 * n1 + 1) * W * (Xa.N * ρ ^ 2 * e) ^ (2 * n1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hWle _) (by positivity)
    _ = _ := by ring

theorem exists_rel {K : Type} [Field K] (σ : K →+* ℂ) (hR : RelIn σ X Xa) (jj : Fin (nd X + 1) → Fin Xa.N) :
    ∃ (Q : MvPolynomial (Fin (nd X + 2)) K) (d : ℕ), (finSuccEquiv K (nd X + 1) Q).coeff 0 ≠ 0 ∧ Q.IsHomogeneous d ∧
      ∀ x ∈ X.dom, eval₂ σ (Fin.cons (Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2)))
        (fun a => Xa.w (jj a) x ^ (2 * (Xa.i * (Xa.g0 / 2)))) : Fin (nd X + 2) → ℂ) Q = 0 := by
  obtain ⟨Q, d, hQ, hh, hv⟩ := hR.2 jj
  have hdense := GlobalTheory.GenFrame.subset_closure_forall_ne_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected (J := Bool) (fun b => cond b Xa.et Xa.th1)
    (fun b => by
      cases b
      · exact Xa.firstTheta_vanishes.1.1.1.1
      · exact Xa.et_sec.1)
    (fun b => by
      cases b
      · exact Xa.firstTheta_ne_zero
      · exact Xa.et_ne)
  obtain ⟨Q', d', h0, hh', hv'⟩ := exists_rel_coeff_zero_ne σ {x | x ∈ X.dom ∧ ∀ b : Bool, cond b Xa.et Xa.th1 x ≠ 0} _
    (fun x hx => mul_ne_zero (hx.2 true) (pow_ne_zero _ (hx.2 false))) d Q hQ hh (fun x hx => hv x hx.1)
  refine ⟨Q', d', h0, hh', fun x hx => ?_⟩
  set u : Fin (nd X + 2) → Frame X.Ψ r → ℂ := Fin.cons (fun x => Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2)))
    fun a x => Xa.w (jj a) x ^ (2 * (Xa.i * (Xa.g0 / 2))) with hu
  have hcont : ContinuousOn (fun x => eval₂ σ (fun i => u i x) Q') X.dom := by
    refine (continuous_eval₂ σ Q').comp_continuousOn (continuousOn_pi.mpr fun i => ?_)
    refine Fin.cases ?_ (fun a => ?_) i
    · exact Xa.et_sec.1.continuousOn.mul (Xa.firstTheta_vanishes.1.1.1.1.continuousOn.pow _)
    · exact (Xa.w_van (jj a)).1.1.1.1.continuousOn.pow _
  have hz : eval₂ σ (fun i => u i x) Q' = 0 := by
    have h1 := ((hcont x hx).mono (fun y hy => hy.1 :
      {x | x ∈ X.dom ∧ ∀ b : Bool, cond b Xa.et Xa.th1 x ≠ 0} ⊆ X.dom)).mem_closure (t := {0}) (hdense hx)
      (fun y hy => hv' y hy)
    simpa using h1
  convert hz using 2
  funext i
  refine Fin.cases rfl (fun a => rfl) i

end Model

theorem forms_not_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hR sf
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < (1 / ((n : ℝ) + 1)) * ‖sf 0 x‖ ^ 2 ∧
      ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra h
    push Not at h
    exact hcon ⟨_, _, Nat.one_div_pos_of_nat (n := n), Nat.one_div_pos_of_nat (n := n), h⟩
  choose xs hxs hs hw using hseq
  set k := 2 * (Xa.i * (Xa.g0 / 2)) with hk
  have hk0 : 0 < k := by
    have h1 := Xa.i_pos
    have h2 := Xa.genus_pos
    obtain ⟨m, hm⟩ := Xa.genus_even
    have : 0 < Xa.g0 / 2 := by omega
    positivity
  set ρ : ℕ → ℝ := fun n => ‖fun j => Xa.w j (xs n)‖ with hρ
  have hρ0 : ∀ n, 0 < ρ n := fun n => by
    obtain ⟨j, hj⟩ := Xa.w_nz _ (hxs n)
    exact norm_pos_iff.mpr fun h => hj (congrFun h j)
  set u : ℕ → Fin Xa.N → ℂ := fun n j => ((ρ n : ℂ))⁻¹ * Xa.w j (xs n) with hu
  have hnρ : ∀ n, ‖((ρ n : ℂ))⁻¹‖ = (ρ n)⁻¹ := fun n => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hρ0 n).le]
  have hu1 : ∀ n, u n ∈ Metric.sphere (0 : Fin Xa.N → ℂ) 1 := fun n => by
    have : u n = ((ρ n : ℂ))⁻¹ • fun j => Xa.w j (xs n) := rfl
    rw [mem_sphere_zero_iff_norm, this, norm_smul, hnρ]
    exact inv_mul_cancel₀ (hρ0 n).ne'
  obtain ⟨ζ, hζ, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin Xa.N → ℂ) 1).tendsto_subseq hu1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  have hε : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hlin : ∀ i, Tendsto (fun n => ‖∑ j, t (i, j) * u (φ n) j‖ ^ 2) atTop (𝓝 (‖∑ j, t (i, j) * ζ j‖ ^ 2)) := fun i =>
    ((tendsto_finsetSum _ fun j _ => ((continuous_apply j).continuousAt.tendsto.comp hlim).const_mul _).norm).pow 2
  have hsu : ∀ i n, ‖∑ j, t (i, j) * u n j‖ ^ 2 = (ρ n)⁻¹ ^ 2 * ‖sf i (xs n)‖ ^ 2 := fun i n => by
    have : ∑ j, t (i, j) * u n j = ((ρ n : ℂ))⁻¹ * sf i (xs n) := by
      simp only [hu, sf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, norm_mul, hnρ, mul_pow]
  have hzero : ∀ i : Fin (nd X), ∑ j, t (i.succ, j) * ζ j = 0 := fun i => by
    have h1 := le_of_tendsto_of_tendsto' (hlin i.succ) (hε.mul (hlin 0)) (fun n => by
      rw [hsu, hsu, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (Finset.single_le_sum (f := fun i : Fin (nd X) => ‖sf i.succ (xs (φ n))‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)).trans (hs (φ n)).le)
    rw [zero_mul] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (by positivity)))
  obtain ⟨jj, hjj⟩ := GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero K σ (nd X) Xa.N (fun p => t (p.1.succ, p.2)) ζ (fun Q hQ => by
    have hinj : Function.Injective (fun p : Fin (nd X) × Fin Xa.N => ((p.1.succ, p.2) : Fin (nd X + 1) × Fin Xa.N)) :=
      (Fin.succ_injective _).prodMap Function.injective_id
    have := ht (rename _ Q) (fun h => hQ (rename_injective _ hinj (by rw [h, map_zero])))
    rwa [eval₂_rename] at this) hζ0 hzero
  obtain ⟨Q, d, h0, hh, hv⟩ := exists_rel X Xa σ hR jj
  refine hjj (expand k ((finSuccEquiv K (nd X + 1) Q).coeff 0)) (k * d) ((expand_ne_zero hk0).mpr h0)
    (isHomogeneous_expand (hh.finSuccEquiv_coeff_isHomogeneous 0 d (zero_add d)) k) ?_
  rw [eval₂_expand', ← eval₂_cons_zero]
  obtain ⟨C, hC⟩ := decay_le X Xa
  set b : ℕ → ℂ := fun n => ((ρ n : ℂ))⁻¹ ^ k * (Xa.et (xs n) * Xa.th1 (xs n) ^ (Xa.i * (Xa.g0 / 2))) with hb
  have hb0 : Tendsto (fun n => b (φ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖b (φ n)‖ ^ 2) atTop (𝓝 0) := by
      have h2 := hε.const_mul |C|
      rw [mul_zero] at h2
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
      have h3 := hC _ (hxs (φ n))
      have h4 : C * (∑ k, X.pnorm Xa.L (Xa.w k) (xs (φ n)) ^ 2) ≤ |C| * (1 / ((φ n : ℝ) + 1)) :=
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hw (φ n)).le (abs_nonneg _))
      have h5 : 0 < (ρ (φ n) ^ k) ^ 2 := pow_pos (pow_pos (hρ0 _) _) _
      simp only [hb]
      rw [norm_mul, norm_pow, hnρ, mul_pow, inv_pow, inv_pow, inv_mul_le_iff₀' h5]
      exact h3.trans (mul_le_mul_of_nonneg_right h4 h5.le)
    have h2 := h1.sqrt
    simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h2
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h2
  have hval : ∀ n, eval₂ σ (Fin.cons (b n) (fun a => u n (jj a) ^ k) : Fin (nd X + 2) → ℂ) Q = 0 := fun n => by
    have h1 := eval₂_smul_of_isHomogeneous σ hh (Fin.cons (Xa.et (xs n) * Xa.th1 (xs n) ^ (Xa.i * (Xa.g0 / 2)))
        (fun a => Xa.w (jj a) (xs n) ^ k) : Fin (nd X + 2) → ℂ) (((ρ n : ℂ))⁻¹ ^ k)
    rw [hv _ (hxs n), mul_zero] at h1
    convert h1 using 2
    funext i
    refine Fin.cases rfl (fun a => ?_) i
    simp only [Fin.cons_succ, hu, mul_pow]
  have hT : Tendsto (fun n => (Fin.cons (b (φ n)) (fun a => u (φ n) (jj a) ^ k) : Fin (nd X + 2) → ℂ)) atTop
      (𝓝 (Fin.cons 0 (fun a => ζ (jj a) ^ k) : Fin (nd X + 2) → ℂ)) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    refine Fin.cases hb0 (fun a => ?_) i
    exact ((continuous_apply (jj a)).continuousAt.tendsto.comp hlim).pow k
  have hfin := (continuous_eval₂ σ Q).continuousAt.tendsto.comp hT
  exact tendsto_nhds_unique hfin (tendsto_const_nhds.congr fun n => (hval (φ n)).symm)

end GlobalTheory.Shares.Low
