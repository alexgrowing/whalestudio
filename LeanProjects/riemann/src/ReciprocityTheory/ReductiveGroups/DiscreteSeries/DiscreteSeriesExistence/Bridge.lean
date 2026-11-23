import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def brIdxSum (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * v i

theorem brIdxSum_sub (u v : Fin n → ℝ) : brIdxSum (u - v) = brIdxSum u - brIdxSum v := by
  unfold brIdxSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply]
  ring

theorem brIdxSum_add (u v : Fin n → ℝ) : brIdxSum (u + v) = brIdxSum u + brIdxSum v := by
  unfold brIdxSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply]
  ring

theorem brIdxSum_root (a b : Fin n) : brIdxSum (Formalism.REAL.root a b) = (a : ℕ) - (b : ℕ) := by
  simp [brIdxSum, Formalism.REAL.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem brIdxSum_cdom_sum (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (_hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) :
    brIdxSum (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
  have hsmul : ∀ (r : ℝ) (v : Fin n → ℝ), brIdxSum (r • v) = r * brIdxSum v := by
    intro r v
    unfold brIdxSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Fin n → ℝ),
      brIdxSum (∑ x ∈ s, f x) = ∑ x ∈ s, brIdxSum (f x) := by
    intro ι s f
    unfold brIdxSum
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hsum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsmul, brIdxSum_root]

theorem br_cdom_term_nonpos (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) (a b : Fin n) :
    (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) ≤ 0 := by
  by_cases h0 : c a b = 0
  · simp [h0]
  · have h1 : (a : ℕ) < (b : ℕ) := (hc a b h0).1
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith

theorem brIdxSum_nonpos_of_cdom {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : Formalism.MainNotions.S.CDom ε μ Λ) :
    brIdxSum (Λ - μ) ≤ 0 := by
  unfold Formalism.MainNotions.S.CDom at h
  obtain ⟨c, hc, hΛ⟩ := h
  rw [hΛ, brIdxSum_cdom_sum ε c hc]
  exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b

theorem not_cdom_add_root (ε : Fin n → Bool) (Λ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + root a b) Λ := by
  intro h
  have h1 := brIdxSum_nonpos_of_cdom h
  have hr : root a b = Formalism.REAL.root a b := rfl
  rw [brIdxSum_sub, brIdxSum_add, hr, brIdxSum_root] at h1
  have h2 : (a : ℕ) < (b : ℕ) := hab
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

theorem cdom_antisymm (ε : Fin n → Bool) {μ Λ : Fin n → ℝ} (h₁ : Formalism.MainNotions.S.CDom ε μ Λ)
    (h₂ : Formalism.MainNotions.S.CDom ε Λ μ) : μ = Λ := by
  have hA := brIdxSum_nonpos_of_cdom h₂
  unfold Formalism.MainNotions.S.CDom at h₁
  obtain ⟨c, hc, hΛ⟩ := h₁
  have hB : brIdxSum (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
    rw [hΛ, brIdxSum_cdom_sum ε c hc]
  have hneg : brIdxSum (μ - Λ) = - brIdxSum (Λ - μ) := by
    rw [brIdxSum_sub, brIdxSum_sub]
    ring
  have hsum0 : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    apply le_antisymm
    · exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b
    · linarith
  have hterm : ∀ a b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    intro a b
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ =>
      br_cdom_term_nonpos ε c hc a b)).1 hsum0 a (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => br_cdom_term_nonpos ε c hc a b)).1 h0 b
      (Finset.mem_univ _)
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra hne
    have h1 : (a : ℕ) < (b : ℕ) := (hc a b hne).1
    have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero hne
    have h3 := hterm a b
    have h4 : (c a b : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  have h5 : Λ - μ = 0 := by
    rw [hΛ]
    simp [hc0]
  exact (sub_eq_zero.mp h5).symm

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem br_actM_mem_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {v : D} (hv : v ∈ S) : actM E X v ∈ S := by
  classical
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hXJ : X * Jm ε = Jm ε * X := hX.2
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hXH : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hXJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -X := by rw [h1, neg_mul, mul_assoc, hJJ, mul_one]
  have hexpK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
    intro t
    have hYH : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hXH, smul_neg]
      congr 2
      simp [Complex.conj_ofReal]
    have hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hYJ : Commute ((t : ℂ) • X) (Jm ε) := by
      show (t : ℂ) • X * Jm ε = Jm ε * ((t : ℂ) • X)
      rw [smul_mul_assoc, mul_smul_comm, hXJ]
    simp only [Kset, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hYH,
        ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero]
    · have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
      have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
      have hc := Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hU
      have hc' : NormedSpace.exp (Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹) = NormedSpace.exp ((t : ℂ) • X) := by
        rw [hJi, ← hYJ.eq, mul_assoc, hJJ, mul_one]
      rw [hc', hJi] at hc
      calc NormedSpace.exp ((t : ℂ) • X) * Jm ε
          = Jm ε * NormedSpace.exp ((t : ℂ) • X) * Jm ε * Jm ε := by rw [← hc]
        _ = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by rw [mul_assoc, hJJ, mul_one]
  haveI := hS
  have hWc : IsClosed ((LinearMap.range (D.subtype.comp S.subtype) : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) ∈
      LinearMap.range (D.subtype.comp S.subtype) := by
    intro t
    obtain ⟨w, hw, hwv⟩ := hK _ (hexpK t) v hv
    exact LinearMap.mem_range.mpr ⟨⟨w, hw⟩, hwv⟩
  have hd := hD.deriv X hX.1 v
  have hlim : ((actM E X v : D) : H) ∈ LinearMap.range (D.subtype.comp S.subtype) :=
    hWc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ t⁻¹ (Submodule.sub_mem _ (hmem _) (hmem _)))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hlim
  have hy' : (y : D) = actM E X v := Subtype.ext (by simpa using hy)
  rw [← hy']
  exact y.2

theorem isKStableSub_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v) :
    IsKStableSub ε E S := by
  classical
  intro a b hab v hv
  have hact : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (w : D), actM E X w = ∑ i, ∑ j, X i j • E i j w := by
    intro X w
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  have key : ∀ (c : ℂ) (p q : Fin n),
      (∑ i, ∑ j, (if i = p ∧ j = q then c else 0) • E i j v) = c • E p q v := by
    intro c p q
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    all_goals first
      | (intro x _ hx; simp [hx])
      | simp
  have hinK : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → X * Jm ε = Jm ε * X → inK ε X := by
    intro X h1 h2
    refine ⟨?_, h2⟩
    show Xᴴ * Jm ε + Jm ε * X = 0
    rw [h1, neg_mul, h2, neg_add_cancel]
  have hcommJ : ∀ z : ℂ, (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) +
      (if i = b ∧ j = a then z else 0) : Matrix (Fin n) (Fin n) ℂ) * Jm ε =
      Jm ε * (Matrix.of fun i j => (if i = a ∧ j = b then z else 0) +
      (if i = b ∧ j = a then z else 0)) := by
    intro z
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h1 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hab]
      ring
    · by_cases h2 : i = b ∧ j = a
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hab]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  set X₁ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then (1 : ℂ) else 0) +
      (if i = b ∧ j = a then (-1 : ℂ) else 0) with hX₁
  set X₂ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (if i = a ∧ j = b then Complex.I else 0) +
      (if i = b ∧ j = a then Complex.I else 0) with hX₂
  have hJ₁ : X₁ * Jm ε = Jm ε * X₁ := by
    ext i j
    simp only [hX₁, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    by_cases h1 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h1
      rw [hab]
      ring
    · by_cases h2 : i = b ∧ j = a
      · obtain ⟨rfl, rfl⟩ := h2
        rw [hab]
        ring
      · rw [if_neg h1, if_neg h2]
        ring
  have hJ₂ : X₂ * Jm ε = Jm ε * X₂ := hcommJ Complex.I
  have hH₁ : X₁ᴴ = -X₁ := by
    ext i j
    simp only [hX₁, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
    have e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    have e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    simp only [e1, e2]
    split_ifs <;> simp [Complex.star_def, Complex.conj_I]
  have hH₂ : X₂ᴴ = -X₂ := by
    ext i j
    simp only [hX₂, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
    have e1 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    have e2 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    simp only [e1, e2]
    split_ifs <;> simp [Complex.star_def, Complex.conj_I]
  have m₁ := br_actM_mem_of_kStable hσ hD S hS hK (hinK X₁ hH₁ hJ₁) hv
  have m₂ := br_actM_mem_of_kStable hσ hD S hS hK (hinK X₂ hH₂ hJ₂) hv
  have e₁ : actM E X₁ v = E a b v + (-1 : ℂ) • E b a v := by
    rw [hact, hX₁]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]
    rw [key, key, one_smul]
  have e₂ : actM E X₂ v = Complex.I • E a b v + Complex.I • E b a v := by
    rw [hact, hX₂]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib]
    rw [key, key]
  have e₃ : E a b v = (1 / 2 : ℂ) • (actM E X₁ v - Complex.I • actM E X₂ v) := by
    rw [e₁, e₂, smul_add, smul_smul, smul_smul, Complex.I_mul_I]
    module
  rw [e₃]
  exact S.smul_mem _ (S.sub_mem m₁ (S.smul_mem _ m₂))

end Rep

end ReciprocityTheory.ChartRestriction.DS
