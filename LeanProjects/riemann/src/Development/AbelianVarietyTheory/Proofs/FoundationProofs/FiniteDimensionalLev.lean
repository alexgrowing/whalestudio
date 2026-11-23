import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponentialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInvStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalFixedFieldMapOfFiniteIndexStatement

noncomputable section
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.K4.LevFin

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exists_im_gt {S : Set ℂ} (hS : S ∈ Filter.codiscreteWithin Hs) (y : ℝ) : ∃ z ∈ S, y < z.im := by
  set Y := max y 0 + 1 with hY
  set w : ℂ := Complex.I * Y
  have hwim : w.im = Y := by simp [w]
  have h0Y : 0 ≤ max y 0 := le_max_right _ _
  have hyY : y ≤ max y 0 := le_max_left _ _
  have hw : w ∈ Hs := by
    show 0 < w.im
    rw [hwim]; linarith
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hS w hw
  have h2 : {z : ℂ | max y 0 < z.im} ∈ nhdsWithin w {w}ᶜ :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (show max y 0 < w.im by rw [hwim]; linarith))
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  have hz2' : max y 0 < z.im := hz2
  rcases hz1 with h | h
  · exact ⟨z, h, by linarith⟩
  · exact absurd (show 0 < z.im by linarith) h

theorem exponent_int (X : Tower Ω ε) (h : X.K) (hT : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  obtain ⟨φ, C, hφ, hsum⟩ := X.an_exp h
  have hmob : ∀ z : ℂ, mob (ofSL ModularGroup.T) z = z + 1 := by
    intro z
    have he : ∀ i j, ent (ofSL ModularGroup.T) i j = ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) :=
      fun _ _ => rfl
    simp [mob, he, ModularGroup.coe_T]
  have h1 := X.an_sl (ofSL ModularGroup.T) h φ hφ
  rw [hT, hφ] at h1
  simp only [hmob] at h1
  have hev : {z : ℂ | φ z = φ (z + 1)} ∈ Filter.codiscreteWithin Hs := Filter.Germ.coe_eq.mp h1
  let d : ℚ → ℂ := fun r => ε ((X.exp h).coeff r) * (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) - 1)
  have hs : ∀ z : ℂ, C < z.im →
      HasSum (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ (z + 1) - φ z) := by
    intro z hz
    have := (hsum (z + 1) (by simpa using hz)).sub (hsum z hz)
    have e : (fun r : ℚ => d r * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) = fun r : ℚ =>
        ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (z + 1)) -
          ε ((X.exp h).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) := by
      funext r
      simp only [d]
      rw [mul_add, mul_one, Complex.exp_add]
      ring
    rw [e]
    exact this
  have hd : d = 0 := by
    refine GlobalTheory.KExp.uniq d ?_ {z | C < z.im ∧ φ z = φ (z + 1)} ?_ (Complex.I * (|C| + 1)) ?_ ?_
    · refine (X.exp h).isWF_support.mono ?_
      intro r hr
      by_contra hn
      apply hr
      have : (X.exp h).coeff r = 0 := by simpa [HahnSeries.support] using hn
      simp [d, this]
    · intro z hz
      have := hs z hz.1
      rwa [← hz.2, sub_self] at this
    · refine (hs _ ?_).summable
      simp; have := le_abs_self C; linarith
    · intro y
      obtain ⟨z, hz, hy⟩ := exists_im_gt hev (max y C)
      exact ⟨z, ⟨lt_of_le_of_lt (le_max_right _ _) hy, hz⟩, lt_of_le_of_lt (le_max_left _ _) hy⟩
  have h2 := congrFun hd r
  simp only [d, Pi.zero_apply, mul_eq_zero, map_eq_zero, hr, false_or, sub_eq_zero] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = n := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

theorem eq_const_of_nonneg (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := exponent_int X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

theorem mem_adjoin_j (X : Tower Ω ε) : ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  obtain ⟨ψ, hψa, hψ⟩ := X.j_hol
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := exponent_int X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

theorem hol_of_mem_adjoin (X : Tower Ω ε) (b : X.K) (hb : b ∈ Algebra.adjoin Ω {X.jK}) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an b = (φ : Mero) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ψ, hψa, hψ⟩ := X.j_hol
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨ψ, hψ, hψa⟩
  | algebraMap c => exact ⟨fun _ => ε c, differentiableOn_const _, X.an_c c⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a + b, ha.add hb, by rw [map_add, ha', hb']; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨a * b, ha.mul hb, by rw [map_mul, ha', hb']; rfl⟩

theorem hol_of_isIntegral (X : Tower Ω ε) (y : X.K) (hy : IsIntegral (Algebra.adjoin Ω {X.jK}) y) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an y = (φ : Mero) := by
  have hcongr := @SiegelModel.germ_eq_of_eqOn
  have hid := GlobalTheory.FN.germ_main.2.1
  have hunit := GlobalTheory.FN.germ_main.2.2
  obtain ⟨P, hPm, hP⟩ := hy
  set n := P.natDegree with hn
  choose r hrd hran using fun i : Fin n => hol_of_mem_adjoin X _ (P.coeff i).2
  have heq : X.an y ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * X.an y ^ (i : ℕ) = 0 := by
    have h0 := congrArg X.an hP
    rw [hPm.as_sum] at h0
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, map_zero] at h0
    rw [← hn, Finset.sum_range (fun i => X.an (algebraMap _ X.K (P.coeff i)) * X.an y ^ i)] at h0
    rw [← h0]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hran i]; rfl
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero y
  have hbz : ∃ z ∈ Hs, b z ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hb0
    have := hcongr (φ := b) (ψ := fun _ => 0) hc
    rw [this]; rfl
  have hF : ((fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) : Mero) = 0 := by
    have e1 : (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) : ℂ → ℂ) =
        a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i) := by
      funext z; simp [Finset.sum_apply]
    rw [e1]
    have e2 : ((a ^ n + ∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i) : ℂ → ℂ) : Mero) =
        (a : Mero) ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * (a : Mero) ^ (i : ℕ) * (b : Mero) ^ (n - i) := by
      have := map_add (Filter.Germ.coeRingHom (R := ℂ) (Filter.codiscreteWithin Hs)) (a ^ n)
        (∑ i : Fin n, r i * a ^ (i : ℕ) * b ^ (n - i))
      simp only [map_sum, map_mul, map_pow] at this
      exact this
    rw [e2, ← hab]
    calc (X.an y * (b : Mero)) ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * (X.an y * (b : Mero)) ^ (i : ℕ) *
          (b : Mero) ^ (n - i)
        = (b : Mero) ^ n * (X.an y ^ n + ∑ i : Fin n, ((r i : ℂ → ℂ) : Mero) * X.an y ^ (i : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, mul_comm ((b : Mero) ^ n)]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hi : (i : ℕ) ≤ n := i.2.le
          rw [mul_pow, ← pow_mul_pow_sub (b : Mero) hi]
          ring
      _ = 0 := by rw [heq, mul_zero]
  have hFd : DifferentiableOn ℂ (fun z => a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i)) Hs := by
    refine (ha.pow n).add (DifferentiableOn.fun_sum (fun i _ => ((hrd i).mul (ha.pow _)).mul (hb.pow _)))
  have hFz : ∀ z ∈ Hs, a z ^ n + ∑ i : Fin n, r i z * a z ^ (i : ℕ) * b z ^ (n - i) = 0 := by
    intro z hz
    exact hid _ (fun _ => (0 : ℂ)) hFd (differentiableOn_const 0) (by rw [hF]; rfl) z hz
  obtain ⟨h0, hh0, hah0, -⟩ := GlobalTheory.quotient_integral_holomorphic Hs n a b r GlobalTheory.FN.isOpen_Hs
    GlobalTheory.FN.isPreconnected_Hs ha hb hrd hbz hFz
  have hbu : IsUnit (b : Mero) := (hunit b hb hb0).2
  refine ⟨h0, hh0, ?_⟩
  have e : (a : Mero) = ((h0 : ℂ → ℂ) : Mero) * (b : Mero) := by
    rw [hcongr (φ := a) (ψ := h0 * b) hah0]; rfl
  rw [e] at hab
  exact hbu.mul_right_cancel hab

theorem sl_aeval (X : Tower Ω ε) (γ : SL(2, ℤ)) (P : Polynomial Ω) :
    X.sl (ofSL γ) (Polynomial.aeval X.jK P) = Polynomial.aeval X.jK P := by
  have := Polynomial.aeval_algHom_apply (X.sl (ofSL γ)) X.jK P
  rw [X.j_inv] at this
  exact this.symm

theorem exists_eq_div (X : Tower Ω ε) (f : X.K) (hf : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) :
    ∃ P Q : Polynomial Ω, f = Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q := by
  obtain ⟨p, hp0, hpi⟩ := (IntermediateField.isAlgebraic_adjoin_iff.1 (X.alg_j f)).exists_integral_multiple
  have hpf : p • f = (p : X.K) * f := rfl
  rw [hpf] at hpi
  have hrange : ∀ b ∈ Algebra.adjoin Ω {X.jK}, ∃ Q : Polynomial Ω, Polynomial.aeval X.jK Q = b := by
    intro b hb
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    exact hb
  obtain ⟨Q, hQ⟩ := hrange _ p.2
  have hmem := mem_adjoin_j X ((p : X.K) * f) (fun γ => by rw [map_mul, hf, ← hQ, sl_aeval])
    (hol_of_isIntegral X _ hpi)
  obtain ⟨P, hP⟩ := hrange _ hmem
  have hp0' : (p : X.K) ≠ 0 := fun h => hp0 (Subtype.ext h)
  refine ⟨P, Q, ?_⟩
  rw [hP, hQ]
  field_simp

end GlobalTheory.K4.LevFin

namespace GlobalTheory.K4

theorem finiteDimensional_lev : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε)
    (Γ' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ' →
    letI := GlobalTheory.K4.algRat X Γ'; FiniteDimensional (RatFunc Ω) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ ε X Γ' M hM hle
  letI := GlobalTheory.K4.algRat X Γ'
  letI : Algebra (RatFunc Ω) X.K := ((lev X Γ').subtype.comp (jRat X Γ')).toAlgebra
  have hpoly : ∀ P : Polynomial Ω,
      algebraMap (RatFunc Ω) X.K (algebraMap (Polynomial Ω) (RatFunc Ω) P) = Polynomial.aeval X.jK P := by
    intro P
    rw [← coe_jPoly X Γ', ← jRat_algebraMap]
    rfl
  have hfix : ∀ (γ : SL(2, ℤ)) (R : RatFunc Ω),
      X.sl (ofSL γ) (algebraMap (RatFunc Ω) X.K R) = algebraMap (RatFunc Ω) X.K R := by
    intro γ R
    rw [← RatFunc.num_div_denom R, map_div₀, map_div₀, hpoly, hpoly, LevFin.sl_aeval, LevFin.sl_aeval]
  let act : SL(2, ℤ) →* (X.K ≃ₐ[RatFunc Ω] X.K) :=
    { toFun := fun γ => AlgEquiv.ofRingEquiv (f := (X.sl (ofSL γ⁻¹)).toRingEquiv) (hfix γ⁻¹)
      map_one' := by
        ext f
        show X.sl (ofSL 1⁻¹) f = f
        rw [inv_one, map_one, X.sl_one]
      map_mul' := by
        intro g h
        ext f
        show X.sl (ofSL (g * h)⁻¹) f = X.sl (ofSL g⁻¹) (X.sl (ofSL h⁻¹) f)
        rw [mul_inv_rev, map_mul, X.sl_mul] }
  have hact : ∀ γ f, act γ f = X.sl (ofSL γ⁻¹) f := fun _ _ => rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  have hfi : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hfin := GlobalTheory.T.finiteDimensional_fixedField_map_of_finiteIndex' SL(2, ℤ) act Γ' hfi (by
    intro x hx
    obtain ⟨P, Q, hPQ⟩ := LevFin.exists_eq_div X x (fun γ => by
      have := hx γ⁻¹
      rwa [hact, inv_inv] at this)
    rw [IntermediateField.mem_bot]
    exact ⟨algebraMap (Polynomial Ω) (RatFunc Ω) P / algebraMap (Polynomial Ω) (RatFunc Ω) Q, by
      rw [map_div₀, hpoly, hpoly, hPQ]⟩)
  let ι : lev X Γ' →ₗ[RatFunc Ω] IntermediateField.fixedField (Γ'.map act) :=
    { toFun := fun f => ⟨f, by
        rw [IntermediateField.mem_fixedField_iff]
        rintro _ ⟨γ, hγ, rfl⟩
        rw [hact]
        exact (mem_lev_iff X Γ' f).1 f.2 _ (inv_mem hγ)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective ι (fun a b h => Subtype.ext
    (congrArg (fun x : IntermediateField.fixedField (Γ'.map act) => (x : X.K)) h))

end GlobalTheory.K4
