import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hms : m ∈ s.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_map, h0, map_zero])
  have hsub : ∀ f : (Σ k, ι k) → ℂ, ∏ i ∈ m.support, f i ^ m i = ∏ i, f i ^ m i := fun f =>
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [hsub, hsub, mul_left_comm]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (∏ s, c (⟨k, s⟩ : Σ k, ι k).fst ^ m ⟨k, s⟩) = ∏ s, c k ^ m ⟨k, s⟩ from rfl,
    Finset.prod_pow_eq_pow_sum, hs m hms k]

theorem analyticAt_eval_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → (Σ k, ι k) → ℂ} {y : E} (hF : ∀ p, AnalyticAt ℂ (fun y => F y p) y) (f : MRing ι) :
    AnalyticAt ℂ (fun y => eval (F y) (map (Int.castRingHom ℂ) f)) y := by
  induction (map (Int.castRingHom ℂ) f) using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hF i)

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem holoOn_eval_lift (R : AnLogRes P J e) (x : R.X) (f : MRing ι) :
    R.A.HoloOn (R.U x) (fun y => eval (R.lift x y) (map (Int.castRingHom ℂ) f)) := by
  intro j w hw
  exact analyticAt_eval_comp (F := fun w => R.lift x ((R.A.chart j).symm w))
    (fun p => R.holo x p j w hw) f

theorem isSection_lift (R : AnLogRes P J e) {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s) :
    IsSection R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) := by
  obtain ⟨a, ha, hsa, -⟩ := hs
  refine ⟨fun x => holoOn_eval_lift R x s, fun x x' y hy => ?_⟩
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  have h1 := A.pos _ (R.mem x y hy.1).1
  have h2 := A.pos _ (R.mem x' y hy.2).1
  have hsm := A.smul c (R.lift x' y) hc
  rw [← hxy] at hsm
  have he : eval (R.lift x y) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval (R.lift x' y) (map (Int.castRingHom ℂ) s) := by
    rw [hxy]
    exact eval_smul_of_isMultiHomog hsa c _
  simp only [potOf]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_log h1, Real.exp_log h2, he, hsm]
  simp only [ha, zpow_natCast, norm_mul, norm_prod, norm_pow]
  have hP : 0 < ∏ k, ‖c k‖ ^ a k :=
    Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hc k)) _
  field_simp

theorem logNormSec_lift (R : AnLogRes P J e) (A : HermLine ι) (s : MRing ι) (y : R.X) :
    logNormSec (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) y =
      logNorm A s (R.lift y y) := by
  have hpos := A.pos _ (R.mem y y (R.mem_U y)).1
  simp only [logNormSec, logNorm, potOf]
  rw [Real.exp_neg, Real.exp_log hpos, div_eq_mul_inv]

end ReciprocityTheory.ChartRestriction.G.Geo
