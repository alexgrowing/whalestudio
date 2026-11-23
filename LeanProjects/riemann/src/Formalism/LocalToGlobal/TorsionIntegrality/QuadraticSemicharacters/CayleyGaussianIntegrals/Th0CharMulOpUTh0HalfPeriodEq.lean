import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section SlopeTestRemainingChoices

theorem altE_std (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] (x y : n → ℂ) :
    altE (stdH L n) x y = ∑ i, Formalism.L2.Th1.F.altE L (x i) (y i) := by
  simp only [altE, stdH_apply, Complex.im_sum, Formalism.L2.Th1.F.altE]

theorem mem_stdLat (L : PeriodPair) (n : Type*) (x : n → ℂ) :
    x ∈ stdLat L n ↔ ∀ i, x i ∈ L.lattice := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem exp_pi_int (k : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = (-1 : ℂ) ^ k := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem neg_one_zpow_pm (k : ℤ) : (-1 : ℂ) ^ k = 1 ∨ (-1 : ℂ) ^ k = -1 := by
  rcases Int.even_or_odd k with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem neg_one_pow_natAbs (k : ℤ) : (-1 : ℂ) ^ k.natAbs = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with h | h
  · rw [h.neg_one_zpow, (Int.natAbs_even.mpr h).neg_one_pow]
  · rw [h.neg_one_zpow, (Int.natAbs_odd.mpr h).neg_one_pow]

theorem cayleyGaussianIntegrals_lin_fact (L : PeriodPair) (s t : ℝ) (a b c : ℂ) :
    Formalism.L2.Th1.F.altE L ((s : ℂ) * a + (t : ℂ) * b) c
      = s * Formalism.L2.Th1.F.altE L a c + t * Formalism.L2.Th1.F.altE L b c := by
  have h : Formalism.L2.Th1.F.herm L ((s : ℂ) * a + (t : ℂ) * b) c
      = (s : ℂ) * Formalism.L2.Th1.F.herm L a c + (t : ℂ) * Formalism.L2.Th1.F.herm L b c := by
    simp only [Formalism.L2.Th1.F.herm]
    ring
  rw [Formalism.L2.Th1.F.altE, h, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  rfl

theorem cayleyGaussianIntegrals_self_fact (L : PeriodPair) (a : ℂ) : Formalism.L2.Th1.F.altE L a a = 0 := by
  have := Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L a a
  linarith

theorem period_skew_form_add_left (L : PeriodPair) (a b c : ℂ) :
    Formalism.L2.Th1.F.altE L (a + b) c = Formalism.L2.Th1.F.altE L a c + Formalism.L2.Th1.F.altE L b c := by
  rw [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Complex.add_im]
  rfl

theorem mem_lattice_of_dual (L : PeriodPair) (u : ℂ)
    (h1 : ∃ m : ℤ, Formalism.L2.Th1.F.altE L u L.ω₁ = (m : ℝ))
    (h2 : ∃ m : ℤ, Formalism.L2.Th1.F.altE L u L.ω₂ = (m : ℝ)) : u ∈ L.lattice := by
  obtain ⟨m₁, h1⟩ := h1
  obtain ⟨m₂, h2⟩ := h2
  have hu := L.basis.sum_repr u
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one, Complex.real_smul, Complex.real_smul] at hu
  set s := L.basis.repr u 0
  set t := L.basis.repr u 1
  have hsw := Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L L.ω₁ L.ω₂
  rw [← hu, cayleyGaussianIntegrals_lin_fact, cayleyGaussianIntegrals_self_fact, hsw] at h1
  rw [← hu, cayleyGaussianIntegrals_lin_fact, cayleyGaussianIntegrals_self_fact] at h2
  have hE := Formalism.L2.Th1.F.altEBasis L
  rw [← hu]
  split_ifs at hE
  · rw [hE] at h1 h2
    refine PeriodPair.mem_lattice.mpr ⟨-m₂, m₁, ?_⟩
    have hs : s = -(m₂ : ℝ) := by linarith
    have ht : t = (m₁ : ℝ) := by linarith
    rw [hs, ht]
    push_cast
    ring
  · rw [hE] at h1 h2
    refine PeriodPair.mem_lattice.mpr ⟨m₂, -m₁, ?_⟩
    have hs : s = (m₂ : ℝ) := by linarith
    have ht : t = -(m₁ : ℝ) := by linarith
    rw [hs, ht]
    push_cast
    ring

theorem semiChar_pm (L : PeriodPair) (ω : ℂ) :
    Formalism.L2.Th1.F.semiChar L ω = 1 ∨ Formalism.L2.Th1.F.semiChar L ω = -1 := by
  unfold Formalism.L2.Th1.F.semiChar
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem th0Char_pm (L : PeriodPair) (ω₀ ω : ℂ) (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = 1 ∨ Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = -1 := by
  obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L ω ω₀ h h0
  rw [Formalism.L2.Th1.F.thetaZeroCharacter, hk, exp_pi_int]
  rcases semiChar_pm L ω with h1 | h1 <;> rcases neg_one_zpow_pm k with h2 | h2 <;> rw [h1, h2] <;>
    norm_num

theorem th0Char_sq (L : PeriodPair) (ω₀ ω : ℂ) (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω * Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω = 1 := by
  rcases th0Char_pm L ω₀ ω h0 h with h1 | h1 <;> rw [h1] <;> norm_num

theorem th0Char_zero (L : PeriodPair) (ω₀ : ℂ) : Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ 0 = 1 := by
  simp [Formalism.L2.Th1.F.thetaZeroCharacter, Formalism.L2.Th1.F.semiChar, Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm]

theorem th0Char_add (L : PeriodPair) (ω₀ x y : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ (x + y)
      = Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ x * Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ y
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.F.altE L x y : ℂ)) := by
  simp only [Formalism.L2.Th1.F.thetaZeroCharacter]
  rw [Formalism.L2.Th1.F.semiCharMul L x y hx hy, period_skew_form_add_left]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem stdChar_single (L : PeriodPair) (ω₀ : ℂ) {n : Type*} [Fintype n] [DecidableEq n] (i : n) (ω : ℂ) :
    stdChar L ω₀ (Pi.single i ω : n → ℂ) = Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω := by
  rw [stdChar, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, th0Char_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem th0Char_mul_opU_th0_half_period_eq (L : PeriodPair) (ω₀ : ℂ) (h0 : ω₀ ∈ L.lattice) (hh : ω₀ / 2 ∉ L.lattice) (ω : ℂ)
    (hω : ω ∈ L.lattice) (z : ℂ) :
    Formalism.L2.Th1.F.thetaZeroCharacter L ω₀ ω * Formalism.L2.Th1.F.opU L ω (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) z
      = Formalism.L2.Th1.F.th0 L (ω₀ / 2) z := by
  have h := (Formalism.L2.Th1.F.th0Basic L ω₀ h0 hh).2.2.2.2 ω hω z
  have hsq := th0Char_sq L ω₀ ω h0 hω
  rw [Formalism.L2.Th1.F.opU, h, ← Formalism.L2.Th1.F.thetaZeroCharacter]
  have he : Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination
    (Formalism.L2.Th1.F.th0 L (ω₀ / 2) z * (Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
              + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
      * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z ω
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2))) * hsq
    + Formalism.L2.Th1.F.th0 L (ω₀ / 2) z * he

end SlopeTestRemainingChoices

theorem StdSelfDual_proof : StdSelfDual := by
  intro L n _ _
  refine AddSubgroup.ext fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩
  · rw [mem_stdLat]
    intro i
    have key : ∀ ω ∈ L.lattice, ∃ m : ℤ, Formalism.L2.Th1.F.altE L (x i) ω = (m : ℝ) := by
      intro ω hω
      have hy : (Pi.single i ω : n → ℂ) ∈ stdLat L n := by
        rw [mem_stdLat]
        intro j
        by_cases hj : j = i
        · subst hj
          rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj]
          exact L.lattice.zero_mem
      obtain ⟨m, hm⟩ := hx _ hy
      refine ⟨m, ?_⟩
      rw [altE_std, Finset.sum_eq_single i] at hm
      · rwa [Pi.single_eq_same] at hm
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.altE, Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    exact mem_lattice_of_dual L (x i) (key _ L.ω₁_mem_lattice) (key _ L.ω₂_mem_lattice)
  · rw [mem_stdLat] at hx hy
    choose k hk using fun i => Formalism.L2.Th1.F.altEInt L (x i) (y i) (hx i) (hy i)
    refine ⟨∑ i, k i, ?_⟩
    rw [altE_std]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hk i

theorem StdSemiChar_proof : StdSemiChar := by
  intro L ω₀ n _ _ h0
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [mem_stdLat] at hx
    unfold stdChar
    refine Finset.prod_induction _ (fun c : ℂ => c = 1 ∨ c = -1) ?_ (Or.inl rfl)
      (fun i _ => th0Char_pm L ω₀ (x i) h0 (hx i))
    intro a b ha hb
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · rw [mem_stdLat] at hx hy
    simp only [stdChar, Pi.add_apply]
    rw [altE_std, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => th0Char_add L ω₀ (x i) (y i) (hx i) (hy i)

theorem product_theta_mem : ProductThetaMem := by
  intro L ω₀ n _ _ h0 hh α hα
  obtain ⟨hd, h1, -⟩ := Formalism.L2.Th1.F.th0Basic L ω₀ h0 hh
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z _
    unfold F0 prodFn
    refine Finset.analyticAt_fun_prod _ fun i _ => ?_
    exact (hd.analyticAt (z i)).comp_of_eq
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) i).analyticAt z) rfl
  · intro x hx z
    rw [hα x hx, F0, heisenbergStandard, stdChar, ← Finset.prod_mul_distrib, prodFn]
    rw [mem_stdLat] at hx
    exact Finset.prod_congr rfl fun i _ => th0Char_mul_opU_th0_half_period_eq L ω₀ h0 hh (x i) (hx i) (z i)
  · simp [F0, prodFn, h1]

theorem th_split (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h0 : ω₀ ∈ L.lattice)
    (hh : ω₀ / 2 ∉ L.lattice) (α : (n → ℂ) → ℂ) (hα : ∀ x ∈ stdLat L n, α x = stdChar L ω₀ x)
    (G : (n → ℂ) → ℂ) (hG : G ∈ Th (stdH L n) α (stdLat L n)) (w : n → ℂ) (i : n) :
    G w = G (Function.update w i 0) * Formalism.L2.Th1.F.th0 L (ω₀ / 2) (w i) := by
  obtain ⟨hGa, hGf⟩ := hG
  have hu : Differentiable ℂ (fun t : ℂ => Function.update w i t) := by
    rw [differentiable_pi]
    intro j
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne h]
      exact differentiable_const _
  have hGd : Differentiable ℂ G := fun z => (hGa z (Set.mem_univ z)).differentiableAt
  have hline := Formalism.L2.Th1.F.th0Line L ω₀ (fun t => G (Function.update w i t)) h0 hh (hGd.comp hu) ?_
    (w i)
  · simpa only [Function.update_eq_self] using hline
  · intro ω hω t
    have hx : (Pi.single i ω : n → ℂ) ∈ stdLat L n := by
      rw [mem_stdLat]
      intro j
      by_cases hj : j = i
      · subst hj
        rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj]
        exact L.lattice.zero_mem
    have hfix := hGf _ hx (Function.update w i t)
    have hsum : Function.update w i t + Pi.single i ω = Function.update w i (t + ω) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have hH1 : stdH L n (Function.update w i t) (Pi.single i ω) = Formalism.L2.Th1.F.herm L t ω := by
      rw [stdH_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hH2 : stdH L n (Pi.single i ω) (Pi.single i ω) = Formalism.L2.Th1.F.herm L ω ω := by
      rw [stdH_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp [Formalism.L2.Th1.F.herm]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hα _ hx, stdChar_single, opU, hsum, hH1, hH2] at hfix
    have hsq := th0Char_sq L ω₀ ω h0 hω
    have he : Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    show G (Function.update w i (t + ω)) = _
    rw [← hfix]
    linear_combination
      (-(G (Function.update w i (t + ω))) * (Complex.exp ((Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          + (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2)
        * Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L t ω
          - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L ω ω / 2))) * hsq
      - G (Function.update w i (t + ω)) * he

theorem ThStd_proof : ThStd := by
  intro L ω₀ n _ _ h0 hh α hα G hG
  have key : ∀ (s : Finset n) (z : n → ℂ),
      G z = (∏ i ∈ s, Formalism.L2.Th1.F.th0 L (ω₀ / 2) (z i)) * G (fun j => if j ∈ s then 0 else z j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro z; simp
    | insert i s hi ih =>
      intro z
      rw [ih z, th_split L ω₀ n h0 hh α hα G hG (fun j => if j ∈ s then 0 else z j) i,
        Finset.prod_insert hi]
      have h1 : Function.update (fun j => if j ∈ s then 0 else z j) i 0
          = fun j => if j ∈ insert i s then 0 else z j := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Finset.mem_insert, hj]
      rw [h1]
      simp only [hi, if_false]
      ring
  funext z
  have h := key Finset.univ z
  simp only [Finset.mem_univ, if_true] at h
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul, F0, prodFn]
  rw [mul_comm]
  rfl

theorem cm_th0Char (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (h4 : 4 * (a : ℤ) * c = b ^ 2 + d)
    (hodd : Odd a) (h8 : d % 8 = 7) (m k : ℤ) :
    Formalism.L2.Th1.F.thetaZeroCharacter (Formalism.L2.Th1.F.cmPair a b d ha hd) (a : ℂ)
              ((m : ℂ) * (a : ℂ) + (k : ℂ) * Formalism.L2.Th1.F.cmTheta b d)
      = (-1 : ℂ) ^ (Formalism.L2.Th1.F.cmForm a b c m k) := by
  have hmem0 : (a : ℂ) ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₁_mem_lattice
  have hhalf : (a : ℂ) / 2 ∉ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice :=
    (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₁_div_two_notMem_lattice
  have hmem : (m : ℂ) * (a : ℂ) + (k : ℂ) * Formalism.L2.Th1.F.cmTheta b d
      ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice := PeriodPair.mem_lattice.mpr ⟨m, k, rfl⟩
  obtain ⟨-, h1, -, -, hq⟩ := Formalism.L2.Th1.F.th0Basic (Formalism.L2.Th1.F.cmPair a b d ha hd) (a : ℂ) hmem0 hhalf
  have hA := hq _ hmem 0
  have hB := Formalism.L2.Th1.F.cmTheta0 a b c d ha hd h4 hodd h8 m k 0
  rw [hA, h1, mul_one, mul_one, ← Formalism.L2.Th1.F.thetaZeroCharacter] at hB
  rw [← neg_one_pow_natAbs]
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) hB

theorem CmStdChar_proof : CmStdChar := by
  intro a b c d ha hd h4 hodd h8 n _ _ x hx
  rw [mem_stdLat] at hx
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [alphaQ, qOf, stdH_apply, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum, stdChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.mp (hx i)
  have hmk' : (m : ℂ) * (a : ℂ) + (k : ℂ) * Formalism.L2.Th1.F.cmTheta b d = x i := hmk
  rw [← hmk', cm_th0Char a b c d ha hd h4 hodd h8 m k,
    (Formalism.L2.Th1.F.cmNorm a b c d ha hd h4 m k).2.1, Complex.ofReal_re, ← exp_pi_int]
  congr 3
  field_simp

end Formalism.L2.Th1.H
