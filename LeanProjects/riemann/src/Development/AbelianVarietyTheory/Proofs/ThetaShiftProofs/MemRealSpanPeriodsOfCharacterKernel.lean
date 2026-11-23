import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.PeriodSpan

theorem eq_of_exp_mul_eq {a b : ℂ} (H : ∀ s : ℂ, Complex.exp (s * a) = Complex.exp (s * b)) :
    a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h1 := H (Real.pi * Complex.I / (a - b))
  have h2 : Complex.exp (Real.pi * Complex.I / (a - b) * a - Real.pi * Complex.I / (a - b) * b)
      = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [← mul_sub, div_mul_cancel₀ _ hd, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem exists_block_solution {g : ℕ} (S : Finset (Fin g)) (A : Matrix (Fin g) (Fin g) ℝ)
    (hA : A.PosDef) (y : Fin g → ℝ) :
    ∃ b : Fin g → ℝ, (∀ k ∈ S, b k = 0) ∧ ∀ k ∉ S, A.mulVec b k = y k := by
  classical
  let T : (Fin g → ℝ) →ₗ[ℝ] (Fin g → ℝ) :=
    LinearMap.pi fun k => if k ∈ S then LinearMap.proj k
      else (LinearMap.proj k).comp A.mulVecLin
  have hT : ∀ b k, T b k = if k ∈ S then b k else A.mulVec b k := by
    intro b k
    by_cases hk : k ∈ S <;> simp [T, hk]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    have hpos := hA.dotProduct_mulVec_pos hb0
    have : star b ⬝ᵥ A.mulVec b = 0 := by
      unfold dotProduct
      refine Finset.sum_eq_zero fun k _ => ?_
      have h1 := hT b k
      rw [hb] at h1
      by_cases hk : k ∈ S
      · simp only [hk, if_true, Pi.zero_apply] at h1
        simp [← h1]
      · simp only [hk, if_false, Pi.zero_apply] at h1
        simp [← h1]
    exact hpos.ne' this
  obtain ⟨b, hb⟩ := LinearMap.surjective_of_injective hinj
    (fun k => if k ∈ S then 0 else y k)
  refine ⟨b, fun k hk => ?_, fun k hk => ?_⟩
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm
  · have := hT b k
    rw [hb] at this
    simpa [hk] using this.symm

theorem mem_span_periods : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  classical
  intro g n S h τ p ℓ hn hτ hp hℓ hu z hz
  set R := Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u}
    with hR
  set e : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inl k) 1) with he
  set f : Fin g → Fin g → ℂ := fun k => p (Pi.single (.inr k) 1) with hf
  have hhe : ∀ k, h.mulVec (e k) = Pi.single k 1 := fun k => (hp k).1
  have hhf : ∀ k, h.mulVec (f k) = τ.mulVec (Pi.single k 1) := fun k => (hp k).2
  have hinj : Function.Injective h.mulVec := by
    have hM : h * (Matrix.of fun i k => e k i) = 1 := by
      ext i k
      have := congrFun (hhe k) i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
        using this
    have hM' := mul_eq_one_comm.mp hM
    intro x y hxy
    have := congrArg (Matrix.of fun i k => e k i).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hM'] using this
  have hℓe : ∀ k ∈ S, ∀ k' ∈ S, ℓ k (e k') =
      2 * Real.pi * Complex.I * n * if k' = k then 1 else 0 := by
    intro k hk k' hk'
    refine eq_of_exp_mul_eq fun s => ?_
    have := hℓ k hk k' hk' s
    rw [map_smul, smul_eq_mul, eTwoPi] at this
    rw [he]
    refine this.trans ?_
    congr 1
    ring
  have hre : ∀ r ∈ R, ∀ k ∈ S, (ℓ k r).re = 0 := by
    intro r hr k hk
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu', rfl⟩ := hx
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (hu u hu' k hk)
      rw [hm]
      simp
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx =>
      rw [← Complex.coe_smul, map_smul]
      simp [hx]
  have heR : ∀ k, e k ∈ R := fun k =>
    Submodule.subset_span ⟨Pi.single (.inl k) 1, fun k' _ => by simp, rfl⟩
  have hfR : ∀ k ∉ S, f k ∈ R := fun k hk =>
    Submodule.subset_span ⟨Pi.single (.inr k) 1, fun k' hk' => by
      have : k' ≠ k := fun e => hk (e ▸ hk')
      simp [this], rfl⟩
  obtain ⟨b, hbS, hb⟩ := exists_block_solution S _ hτ fun k => (h.mulVec z k).im
  set c : Fin g → ℂ := h.mulVec z - τ.mulVec fun k => (b k : ℂ) with hc
  have hcim : ∀ k ∉ S, (c k).im = 0 := by
    intro k hk
    have := hb k hk
    simp only [hc, Pi.sub_apply, Complex.sub_im]
    rw [← this]
    simp [Matrix.mulVec, dotProduct]
  have hzeq : z = ∑ k, (b k : ℂ) • f k + ∑ k, c k • e k := by
    apply hinj
    have h1 : ∑ k, (b k : ℂ) • (Pi.single k 1 : Fin g → ℂ) = fun k => (b k : ℂ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : ∑ k, c k • (Pi.single k 1 : Fin g → ℂ) = c := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hhe, hhf, h2]
    simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum, h1]
    rw [hc]; abel
  set r : Fin g → ℂ := ∑ k, (b k : ℂ) • f k + ∑ k, ((c k).re : ℂ) • e k with hr
  have hrR : r ∈ R := by
    refine R.add_mem (R.sum_mem fun k _ => ?_) (R.sum_mem fun k _ => ?_)
    · by_cases hk : k ∈ S
      · simp [hbS k hk]
      · rw [Complex.coe_smul]; exact R.smul_mem _ (hfR k hk)
    · rw [Complex.coe_smul]; exact R.smul_mem _ (heR k)
  have hzr : z = r + ∑ k, (((c k).im : ℂ) * Complex.I) • e k := by
    rw [hr, add_assoc, ← Finset.sum_add_distrib]
    simp only [← add_smul, Complex.re_add_im]
    exact hzeq
  have him : ∀ k, (c k).im = 0 := by
    intro k
    by_cases hk : k ∈ S
    · have h0 := hz k hk
      rw [hzr, map_add, map_sum, Finset.sum_eq_single k] at h0
      · have h1 := congrArg Complex.re h0
        rw [map_smul, hℓe k hk k hk, Complex.add_re, hre r hrR k hk] at h1
        simpa [Real.pi_ne_zero, hn.ne'] using h1
      · intro k' _ hne
        by_cases hk' : k' ∈ S
        · rw [map_smul, hℓe k hk k' hk']
          simp [hne]
        · simp [hcim k' hk']
      · simp
    · exact hcim k hk
  rw [hzr]
  simpa [him] using hrR

end GlobalTheory.PeriodSpan
