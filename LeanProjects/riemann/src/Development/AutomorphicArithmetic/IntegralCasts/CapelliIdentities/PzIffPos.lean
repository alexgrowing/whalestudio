import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh60.Pz :
    {R : Type} → [inst : Ring R] → [Algebra ℝ R] → R → Prop :=
    fun {R : Type} [Ring R] [Algebra ℝ R] (t : R) ↦
      ∃ (s : Finset ℝ),
        (∀ l ∈ s, (0 : ℝ) < l) ∧
          (Polynomial.aeval t : Polynomial ℝ → R) (∏ l ∈ s, (Polynomial.X - (Polynomial.C : ℝ → Polynomial ℝ) l)) = (0 : R)

private theorem UpperTheory.Reformulated.B.Qh60.aux {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ x : W, x ≠ 0 → 0 < inner ℝ (T x) x := by
  classical
  have hn : Module.finrank ℝ W = Module.finrank ℝ W := rfl
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have hev : ∀ i, Module.End.HasEigenvector T (μ i) (b i) := fun i => by
    simpa using hT.hasEigenvector_eigenvectorBasis hn i
  have happ : ∀ i, T (b i) = μ i • b i := fun i => (hev i).apply_eq_smul
  have hne : ∀ i, b i ≠ 0 := fun i => (hev i).2
  have haev : ∀ (s : Finset ℝ) i,
      (Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))) (b i)
        = (∏ l ∈ s, (μ i - l)) • b i := fun s i => by
    rw [Module.End.aeval_apply_of_hasEigenvector (hev i)]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨s, hs, h0⟩ x hx
    have hpos : ∀ i, 0 < μ i := fun i => by
      have h1 := haev s i
      rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
      obtain ⟨l, hl, h2⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_right (hne i))
      rw [sub_eq_zero.1 h2]
      exact hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (b i), happ i, real_inner_smul_right, real_inner_comm (b i) x]
      ring
    have hex : ∃ i, inner ℝ (b i) x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← b.sum_repr' x]
      simp [hc]
    obtain ⟨i, hi⟩ := hex
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hpos i) (by positivity)⟩
  · intro h
    refine ⟨Finset.univ.image μ, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      have h1 := h (b i) (hne i)
      rw [happ i, real_inner_smul_left] at h1
      exact (pos_iff_pos_of_mul_pos h1).2 (real_inner_self_pos.2 (hne i))
    · refine b.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, haev, LinearMap.zero_apply,
        Finset.prod_eq_zero (Finset.mem_image_of_mem μ (Finset.mem_univ i)) (sub_self _), zero_smul]

theorem UpperTheory.Reformulated.B.Qh60.Pz_iff_pos :
    ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : _root_.Module ℝ W] [FiniteDimensional ℝ W] (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ),
      (∀ (x y : W), ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) y : W → ℝ) x) →
        (∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) x) →
          ∀ (T : Module.End ℝ W),
            (∀ (x y : W),
                ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) ((T : W → W) y)) →
              (UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) x) := by
  intro W _ _ _ Q hsymm hpos T hT
  let c : InnerProductSpace.Core ℝ W :=
    { inner := fun x y => Q x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hpos x h).ne' hx }
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ c
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore c.toCore
  exact UpperTheory.Reformulated.B.Qh60.aux T (fun x y => hT x y)
