import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private lemma norm_le_of_integral_image {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : M.det ≠ 0) (v : Fin n → K)
    (h : ∀ i, ‖(((M *ᵥ v) i : K) : PadicAlgCl p)‖ ≤ 1) (i : Fin n) :
    ‖(v i : PadicAlgCl p)‖ ≤ ∑ a, ∑ b, ‖((M⁻¹ a b : K) : PadicAlgCl p)‖ := by
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, u = M *ᵥ v := ⟨_, rfl⟩
  have hv : v = M⁻¹ *ᵥ u := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]
  have hu1 : ∀ b, ‖(u b : PadicAlgCl p)‖ ≤ 1 := by
    intro b
    rw [hu]
    exact h b
  have hrow : ‖(v i : PadicAlgCl p)‖ ≤ ∑ b, ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ := by
    rw [hv]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    calc ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ * ‖(u b : PadicAlgCl p)‖
        ≤ ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hu1 b) (norm_nonneg _)
      _ = ‖((M⁻¹ i b : K) : PadicAlgCl p)‖ := mul_one _
  refine hrow.trans ?_
  exact Finset.single_le_sum (f := fun a => ∑ b, ‖((M⁻¹ a b : K) : PadicAlgCl p)‖)
    (fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ i)

private lemma framePow {p : ℕ} [Fact p.Prime] (k : ℕ) :
    ‖((p ^ k : ℕ) : PadicAlgCl p)‖ = ((p : ℝ) ^ k)⁻¹ := by
  rw [Nat.cast_pow, norm_pow, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
    PadicAlgCl.norm_extends, Padic.norm_p, inv_pow]

theorem UpperTheory.exists_bounded_denominator_of_local_integrality_conj :
    UpperTheory.Gal.W2.FInt → ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (S B : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w)), (∀ w, (S w).det ≠ 0) → (∀ w, (B w).det ≠ 0) → ∃ k : ℕ, ∀ y : Fin G.n → G.F, IntL (G := G) (fun w => S w *ᵥ (fun i => G.embW w (y i))) → IntL (G := G) (fun w => B w *ᵥ (fun i => G.embW w (IsCMField.complexConj G.F (y i)))) → ∃ (m : ℕ) (c : Fin G.n → 𝓞 G.F), m.Coprime p ∧ ∀ i, (c i : G.F) = ((m * p ^ k : ℕ) : G.F) * y i := by
  intro hF p _ G S B hS hB
  classical
  set R : ℝ := ∑ w, ((∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) +
    ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) with hR
  have hnnS : ∀ w, 0 ≤ ∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ :=
    fun w => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  have hnnB : ∀ w, 0 ≤ ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ :=
    fun w => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  have hone : ∀ w, (∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖) +
      ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := fun w =>
    Finset.single_le_sum
      (f := fun w' => (∑ a, ∑ b, ‖(((S w')⁻¹ a b : G.Fw w') : PadicAlgCl p)‖) +
        ∑ a, ∑ b, ‖(((B w')⁻¹ a b : G.Fw w') : PadicAlgCl p)‖)
      (fun w' _ => add_nonneg (hnnS w') (hnnB w')) (Finset.mem_univ w)
  have hSR : ∀ w, ∑ a, ∑ b, ‖(((S w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := by
    intro w
    have h1 := hone w
    have h2 := hnnB w
    linarith
  have hBR : ∀ w, ∑ a, ∑ b, ‖(((B w)⁻¹ a b : G.Fw w) : PadicAlgCl p)‖ ≤ R := by
    intro w
    have h1 := hone w
    have h2 := hnnS w
    linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hp1
  refine ⟨k, fun y hyS hyB => ?_⟩
  have hp0 : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by linarith) k
  have key : ∀ (w : Fin G.m) (z : G.Fw w), ‖(z : PadicAlgCl p)‖ ≤ R →
      ‖((G.embW w ((p ^ k : ℕ) : G.F) * z : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
    intro w z hz
    have hc : ((G.embW w ((p ^ k : ℕ) : G.F) * z : G.Fw w) : PadicAlgCl p)
        = ((p ^ k : ℕ) : PadicAlgCl p) * (z : PadicAlgCl p) := by
      rw [map_natCast]
      push_cast
      rfl
    rw [hc, norm_mul, framePow]
    calc ((p : ℝ) ^ k)⁻¹ * ‖(z : PadicAlgCl p)‖
        ≤ ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (hz.trans hk.le) (inv_nonneg.mpr hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  have hint : ∀ i w,
      ‖((G.embW w (((p ^ k : ℕ) : G.F) * y i) : G.Fw w) : PadicAlgCl p)‖ ≤ 1 ∧
      ‖((G.embW w (IsCMField.complexConj G.F (((p ^ k : ℕ) : G.F) * y i)) : G.Fw w) :
        PadicAlgCl p)‖ ≤ 1 := by
    intro i w
    constructor
    · rw [map_mul]
      exact key w _ ((norm_le_of_integral_image _ (S w) (hS w) (fun j => G.embW w (y j)) (hyS w) i).trans (hSR w))
    · rw [map_mul, map_natCast, map_mul]
      exact key w _ ((norm_le_of_integral_image _ (B w) (hB w)
        (fun j => G.embW w (IsCMField.complexConj G.F (y j))) (hyB w) i).trans (hBR w))
  have hx := fun i => hF p G (((p ^ k : ℕ) : G.F) * y i) (hint i)
  choose m c hmc hc using hx
  refine ⟨∏ i, m i, fun i => ((∏ j ∈ Finset.univ.erase i, m j : ℕ) : 𝓞 G.F) * c i,
    Nat.Coprime.prod_left (fun i _ => hmc i), fun i => ?_⟩
  have hci := hc i
  push_cast at hci ⊢
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  refine (congrArg (fun t => (∏ x ∈ Finset.univ.erase i, (m x : G.F)) * t) hci).trans ?_
  beta_reduce
  ring
