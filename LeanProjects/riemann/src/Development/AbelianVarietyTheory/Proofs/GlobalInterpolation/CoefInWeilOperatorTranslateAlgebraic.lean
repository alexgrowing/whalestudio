import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.CoefWop

lemma Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T (a + b) w = Hf D T a w + Hf D T b w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T w (a + b) = Hf D T w a + Hf D T w b := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

lemma Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (a b : ℕ) (y t : VC D N N') :
    Hf D T (a • y) (b • t) = (a * b : ℂ) * Hf D T y t := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma U_U (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (F : VC D N N' → ℂ) (z : VC D N N') :
    U D T y (U D T t F) z
      = Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) * U D T (y + t) F z := by
  simp only [U]
  rw [show z + y + t = z + (y + t) by abel]
  rw [mul_comm (Complex.exp _) (F _ * _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Hf_add_left, Hf_add_right]
  ring

lemma taylor_const_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G)
    (α : Mono D N N') : taylor D (fun z => c * G z) α = c * taylor D G α := by
  simp only [taylor]
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := (Finsupp.toMultiset α).card) (a := c) (x := (0 : VC D N N'))
    (hG.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun z => c * G z) = c • G from rfl, h]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

lemma contDiff_U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F : VC D N N' → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (U D T x F) := by
  unfold U Hf
  apply ContDiff.mul
  · exact hF.comp (contDiff_id.add contDiff_const)
  · apply ContDiff.cexp
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.div_const
    apply ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    apply ContDiff.mul _ contDiff_const
    exact (contDiff_apply ℂ _ j).comp ((contDiff_apply ℂ _ i).comp (contDiff_apply ℂ _ τ))

lemma sq_one_alg {c : ℂ} {n : ℕ} (hn : 0 < n) (h : c ^ n = 1) : c ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  apply IsIntegral.isAlgebraic
  exact IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

lemma Hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') :
    Hf D T t y = (starRingEnd ℂ) (Hf D T y t) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma wPh_sq (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (y : VC D N N') (m : ℤ) (hm : qH D T y = m) :
    wPh D T p y ^ 2 = 1 := by
  unfold wPh
  split_ifs with hp
  · rw [← Complex.exp_nat_mul, hm]
    have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · have hex : ∃ s : ℂ, ∃ k : ℕ, ∃ m' : ℤ, (p : ℝ) ^ k * qH D T y = m' ∧ s = (-1) ^ m' :=
      ⟨(-1) ^ m, 0, m, by simp [hm], rfl⟩
    obtain ⟨k, m', -, hs⟩ := Classical.epsilon_spec hex
    rw [hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num

lemma root_alg (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℤ)
    (hk : (Hf D T (a • y) (b • t)).im = k) :
    Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) ∈ Qbar := by
  rw [Hf_nsmul] at hk
  have hk' : ((a * b : ℕ) : ℝ) * (Hf D T y t).im = k := by
    rw [← hk]; push_cast
    rw [show ((a : ℂ) * b) = (((a * b : ℝ)) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have hdiff : Hf D T y t - Hf D T t y = 2 * Complex.I * ((Hf D T y t).im : ℂ) := by
    rw [Hf_swap]
    apply Complex.ext <;> simp <;> ring
  apply sq_one_alg (n := 2 * (a * b)) (by positivity)
  rw [hdiff, ← Complex.exp_nat_mul]
  have : ((2 * (a * b) : ℕ) : ℂ) * (-(Real.pi : ℂ) * (2 * Complex.I * ((Hf D T y t).im : ℂ) / 2))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hk'' : ((a * b : ℕ) : ℂ) * ((Hf D T y t).im : ℂ) = (k : ℂ) := by exact_mod_cast hk'
    push_cast at hk'' ⊢
    linear_combination (-(Real.pi : ℂ) * 2 * Complex.I) * hk''
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

end GlobalTheory.CoefWop

namespace GlobalTheory

open GlobalTheory.CoefWop in

theorem coefIn_Wop_U_translate : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  intro D T N N' F Λ p _ y t hF hΛ ⟨b, hb, hbt⟩ ⟨a, ha, hay⟩ hHf ⟨m, hm⟩
  have hfun : Wop D T p y (U D T t F)
      = fun z => (wPh D T p y * Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)))
          * U D T (y + t) F z := by
    funext z
    simp only [Wop, U_U]
    ring
  have hyt : CoefIn D (U D T (y + t) F) Qbar := by
    refine hΛ _ ⟨a * b, by positivity, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul]
    exact Λ.add_mem (Λ.nsmul_mem hay b) (Λ.nsmul_mem hbt a)
  obtain ⟨k, hk⟩ := hHf _ hay _ hbt
  have hw : wPh D T p y ∈ Qbar := sq_one_alg (n := 2) (by norm_num) (wPh_sq D T p y m hm)
  unfold CoefIn
  intro α
  rw [hfun, taylor_const_mul D _ _ (contDiff_U D T _ F hF)]
  exact Qbar.mul_mem (Qbar.mul_mem hw (root_alg D T y t a b ha hb k hk)) (hyt α)

end GlobalTheory
