import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum Filter Topology

namespace PositivityTheory.CW

namespace ExistsNormingFunctional

theorem exists_norming {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) (x₀ : E) :
    ∃ φ : Module.Dual ℂ E, ‖φ x₀‖ = q x₀ ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have H : ∀ c : ℂ, c • x₀ = 0 → (RingHom.id ℂ) c • ((q x₀ : ℝ) : ℂ) = 0 := by
    intro c hc
    have h0 : ‖c‖ * q x₀ = 0 := by rw [← map_smul_eq_mul q, hc, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [norm_eq_zero.1 h]
    · simp [h]
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) :=
    (LinearPMap.mkSpanSingleton' x₀ ((q x₀ : ℝ) : ℂ) H).toFun
  have hf : ∀ (c : ℂ) (h : c • x₀ ∈ Submodule.span ℂ {x₀}), f ⟨c • x₀, h⟩ = c * (q x₀ : ℂ) := by
    intro c h
    exact (LinearPMap.mkSpanSingleton'_apply x₀ ((q x₀ : ℝ) : ℂ) H c h).trans (by simp)
  have h1 : f ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ = (q x₀ : ℂ) :=
    LinearPMap.mkSpanSingleton'_apply_self x₀ ((q x₀ : ℝ) : ℂ) H _
  obtain ⟨g, hg, hgq⟩ := Module.Dual.exists_extension_of_le_seminorm
    (Submodule.span ℂ {x₀}) f (p := q) (by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      exact le_of_eq (map_smul_eq_mul q c x₀).symm)
  refine ⟨g, ?_, hgq⟩
  have h2 := hg ⟨x₀, Submodule.mem_span_singleton_self x₀⟩
  rw [h1] at h2
  rw [show g x₀ = (q x₀ : ℂ) from h2, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]

end ExistsNormingFunctional

private theorem exp_smul_mem_UJset_of_mem_lieSet {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ lieSet ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε := by
  set J := ReciprocityTheory.ChartRestriction.DS.Jm ε with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hX' : Xᴴ * J + J * X = 0 := hX
  set Y : Matrix (Fin n) (Fin n) ℂ := t • X with hYdef
  have hYJ : Yᴴ * J = -(J * Y) := by
    rw [hYdef, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, Matrix.mul_smul,
      eq_neg_of_add_eq_zero_left hX', smul_neg]
  have hY : Yᴴ = J * (-Y) * J := by
    calc Yᴴ = Yᴴ * J * J := by rw [mul_assoc, hJJ, mul_one]
      _ = J * (-Y) * J := by rw [hYJ, mul_neg, neg_mul]
  have hexp : NormedSpace.exp Yᴴ = J * NormedSpace.exp (-Y) * J := by
    have h := Matrix.exp_units_conj u (-Y)
    rw [hY]
    exact h
  have hdet : IsUnit (NormedSpace.exp Y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  show (NormedSpace.exp Y)ᴴ * J * NormedSpace.exp Y = J
  rw [← Matrix.exp_conjTranspose, hexp, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc J J, hJJ, one_mul, Matrix.nonsing_inv_mul _ hdet, mul_one]

theorem d1b : D1 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hCore T₀ hT i
  obtain ⟨q, N, hq, hgrow⟩ := hπ.growth i
  obtain ⟨S, C, I₀, hS, hC, hI₀, hmain⟩ := hCore N
  refine ⟨S, C * ∑ e ∈ I₀, q (T₀ e), hS, ?_⟩
  intro w hw
  obtain ⟨φ, hφ1, hφ2⟩ := ExistsNormingFunctional.exists_norming (p i) (T₀ w)
  have hφc : Continuous φ :=
    hπ.withSeminorms.continuous_normedSpace_rng ℂ φ ⟨{i}, 1, by
      intro x
      simpa using hφ2 x⟩
  let F : H →ₗ[ℂ] Mx n → ℂ :=
    LinearMap.pi (fun g => φ ∘ₗ (π g).toLinearMap ∘ₗ T₀)
  have hF : ∀ v g, F v g = φ (π g (T₀ v)) := fun _ _ => rfl
  have hpos : ∀ g : Mx n, 0 ≤ (1 + hs g) ^ N := by
    intro g
    apply pow_nonneg
    have : 0 ≤ hs g := by
      unfold hs
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hB : 0 ≤ ∑ e ∈ I₀, q (T₀ e) := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have key := hmain F
    (fun v _ => by
      show ContinuousOn (fun g => φ (π g (T₀ v))) (UJset ε)
      exact hφc.comp_continuousOn (hπ.continuousOn (T₀ v)))
    (fun X hX v hv g hg => by
      rw [hF, hT.2 X hX v hv, hasDerivAt_iff_tendsto_slope]
      have hΛ : Continuous fun z : E => φ (π g z) := hφc.comp (π g).continuous
      have heq : slope (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) 0 =
          fun t : ℝ => φ (π g (((t : ℂ))⁻¹ • ((π (NormedSpace.exp (t • X))) (T₀ v) - T₀ v))) := by
        funext t
        rw [slope_def_module]
        simp only [hF, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
          hπ.map_mul g hg _ (exp_smul_mem_UJset_of_mem_lieSet ε X hX t), ContinuousLinearMap.comp_apply, map_smul, map_sub,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_inv]
      rw [heq]
      exact (hΛ.tendsto _).comp (hπ.hasDRep X hX (T₀ v)))
    (fun v _ => ⟨q (T₀ v), fun g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ v))‖ ≤ p i (π g (T₀ v)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ v) := hgrow g hg (T₀ v)
        _ = q (T₀ v) * (1 + hs g) ^ N := mul_comm _ _⟩)
    (∑ e ∈ I₀, q (T₀ e)) hB
    (fun e he g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ e))‖ ≤ p i (π g (T₀ e)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ e) := hgrow g hg (T₀ e)
        _ ≤ (1 + hs g) ^ N * ∑ e ∈ I₀, q (T₀ e) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun e => q (T₀ e)) (fun _ _ => apply_nonneg _ _) he)
            (hpos g)
        _ = (∑ e ∈ I₀, q (T₀ e)) * (1 + hs g) ^ N := mul_comm _ _)
    w hw
  rw [hF, hπ.map_one, ContinuousLinearMap.one_apply] at key
  rw [← hφ1]
  exact key

end PositivityTheory.CW
