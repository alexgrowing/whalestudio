import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem gauss_re (z : GaussianInt) : (z : ℂ).re = z.re := by rw [GaussianInt.toComplex_def₂]

theorem gauss_im (z : GaussianInt) : (z : ℂ).im = z.im := by rw [GaussianInt.toComplex_def₂]

theorem gauss_fin (R0 : ℝ) : {z : GaussianInt | ‖(z : ℂ)‖ ≤ R0}.Finite := by
  have hfin : (Set.Icc (-⌈R0⌉) ⌈R0⌉ ×ˢ Set.Icc (-⌈R0⌉) ⌈R0⌉ : Set (ℤ × ℤ)).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hinj : Set.InjOn (fun z : GaussianInt => (z.re, z.im))
      ((fun z : GaussianInt => (z.re, z.im)) ⁻¹' (Set.Icc (-⌈R0⌉) ⌈R0⌉ ×ˢ Set.Icc (-⌈R0⌉) ⌈R0⌉)) := by
    intro z _ w _ h
    simp only [Prod.mk.injEq] at h
    exact Zsqrtd.ext_iff.mpr ⟨h.1, h.2⟩
  refine (Set.Finite.preimage hinj hfin).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  have key : ∀ n : ℤ, |(n : ℝ)| ≤ R0 → -⌈R0⌉ ≤ n ∧ n ≤ ⌈R0⌉ := by
    intro n hn
    have h1 := abs_le.mp hn
    have h2 := Int.le_ceil R0
    constructor
    · have : ((-⌈R0⌉ : ℤ) : ℝ) ≤ n := by push_cast; linarith [h1.1]
      exact_mod_cast this
    · have : (n : ℝ) ≤ ((⌈R0⌉ : ℤ) : ℝ) := by linarith [h1.2]
      exact_mod_cast this
  have hre : |(z.re : ℝ)| ≤ R0 := by rw [← gauss_re]; exact (Complex.abs_re_le_norm _).trans hz
  have him : |(z.im : ℝ)| ≤ R0 := by rw [← gauss_im]; exact (Complex.abs_im_le_norm _).trans hz
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
  exact ⟨key _ hre, key _ him⟩

theorem fin_bdd (R0 : ℝ) : ∃ R : ℕ, ∀ F : Finset (SpecialLinearGroup (Fin N) GaussianInt),
    (∀ c ∈ F, ∀ c' ∈ F, ∀ i j,
      ‖((((c⁻¹ * c' : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) i j :
        GaussianInt) : ℂ)‖ ≤ R0) → F.card ≤ R := by
  classical
  have h1 : (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N =>
      {z : GaussianInt | ‖(z : ℂ)‖ ≤ R0}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => gauss_fin R0
  refine ⟨h1.toFinset.card, fun F hF => ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp
  refine Finset.card_le_card_of_injOn
    (fun c : SpecialLinearGroup (Fin N) GaussianInt =>
      (((c0⁻¹ * c : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) :
        Fin N → Fin N → GaussianInt)) ?_ ?_
  · intro c hc
    refine Finset.mem_coe.mpr (h1.mem_toFinset.mpr ?_)
    intro i _ j _
    exact hF c0 hc0 c hc i j
  · intro c _ c' _ h
    have h' : c0⁻¹ * c = c0⁻¹ * c' := Subtype.ext h
    exact mul_left_cancel h'

def umat (x : Fin N → Fin N → ℕ × ℕ) : Matrix (Fin N) (Fin N) GaussianInt :=
  fun i j => if i = j then 1 else if i < j then ⟨(x i j).1, (x i j).2⟩ else 0

theorem umat_upper (x : Fin N → Fin N → ℕ × ℕ) : (umat x).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  have h1 : i ≠ j := (ne_of_lt hij').symm
  have h2 : ¬ i < j := not_lt.mpr hij'.le
  simp [umat, h1, h2]

theorem umat_det (x : Fin N → Fin N → ℕ × ℕ) : (umat x).det = 1 := by
  rw [Matrix.det_of_upperTriangular (umat_upper x)]
  simp [umat]

def uel (x : Fin N → Fin N → ℕ × ℕ) : SpecialLinearGroup (Fin N) GaussianInt := ⟨umat x, umat_det x⟩

private theorem coe_uel_eq_umat (x : Fin N → Fin N → ℕ × ℕ) :
    ((uel x : SpecialLinearGroup (Fin N) GaussianInt) : Matrix (Fin N) (Fin N) GaussianInt) = umat x :=
  rfl

theorem count (s0 : Fin N → ℝ) : ∃ F : Finset (SpecialLinearGroup (Fin N) GaussianInt),
    (∀ c ∈ F, ((c : Matrix (Fin N) (Fin N) GaussianInt).map GaussianInt.toComplex).BlockTriangular id ∧
      ∀ i j, i ≤ j → ‖(((c : Matrix (Fin N) (Fin N) GaussianInt) i j : GaussianInt) : ℂ)‖ ≤
        2 * Real.exp (s0 i - s0 j)) ∧
    ENNReal.ofReal (Real.exp (2 * Phi s0)) ≤ F.card := by
  classical
  set K : Fin N → Fin N → ℕ := fun i j => ⌈Real.exp (s0 i - s0 j)⌉₊ with hK
  set S : Finset (Fin N → Fin N → ℕ × ℕ) := Fintype.piFinset fun i => Fintype.piFinset fun j =>
    if i < j then Finset.range (K i j) ×ˢ Finset.range (K i j) else {((0 : ℕ), (0 : ℕ))} with hS
  have hmem : ∀ x ∈ S, ∀ i j, x i j ∈
      (if i < j then Finset.range (K i j) ×ˢ Finset.range (K i j) else {((0 : ℕ), (0 : ℕ))}) := by
    intro x hx i j
    exact Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hx i) j
  have hsmall : ∀ i j (n : ℕ), n < K i j → (n : ℝ) ≤ Real.exp (s0 i - s0 j) := by
    intro i j n hn
    have h1 : (n : ℝ) + 1 ≤ (K i j : ℝ) := by exact_mod_cast hn
    have h2 : (K i j : ℝ) < Real.exp (s0 i - s0 j) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  refine ⟨S.image uel, ?_, ?_⟩
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    rw [coe_uel_eq_umat]
    refine ⟨?_, ?_⟩
    · intro i j hij
      simp [Matrix.map_apply, umat_upper x hij]
    · intro i j hij
      rcases hij.lt_or_eq with h | rfl
      · have hx' := hmem x hx i j
        rw [if_pos h, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx'
        have e : umat x i j = ⟨((x i j).1 : ℤ), ((x i j).2 : ℤ)⟩ := by simp [umat, h.ne, h]
        rw [e]
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [gauss_re, gauss_im]
        have a1 := hsmall i j _ hx'.1
        have a2 := hsmall i j _ hx'.2
        show |((((x i j).1 : ℤ)) : ℝ)| + |(((x i j).2 : ℤ) : ℝ)| ≤ _
        rw [Int.cast_natCast, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (Nat.cast_nonneg _)]
        linarith
      · norm_num [umat]
  · rw [Finset.card_image_of_injOn]
    · rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      rw [hS]
      simp only [Fintype.card_piFinset, apply_ite Finset.card, Finset.card_product, Finset.card_range,
        Finset.card_singleton]
      push_cast
      unfold Phi
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      intro i _
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le)
      intro j _
      split_ifs with h
      · rw [show 2 * (s0 i - s0 j) = (s0 i - s0 j) + (s0 i - s0 j) by ring, Real.exp_add]
        have hc := Nat.le_ceil (Real.exp (s0 i - s0 j))
        exact mul_le_mul hc hc (Real.exp_pos _).le (Nat.cast_nonneg _)
      · simp
    · intro x hx y hy hxy
      funext i j
      have hx' := hmem x hx i j
      have hy' := hmem y hy i j
      by_cases h : i < j
      · have e := congrArg
          (fun g : SpecialLinearGroup (Fin N) GaussianInt => (g : Matrix (Fin N) (Fin N) GaussianInt) i j) hxy
        simp only [coe_uel_eq_umat, umat, h.ne, h, if_false, if_true] at e
        have e1 := congrArg Zsqrtd.re e
        have e2 := congrArg Zsqrtd.im e
        simp only [Nat.cast_inj] at e1 e2
        exact Prod.ext e1 e2
      · rw [if_neg h, Finset.mem_singleton] at hx' hy'
        rw [hx', hy']

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
