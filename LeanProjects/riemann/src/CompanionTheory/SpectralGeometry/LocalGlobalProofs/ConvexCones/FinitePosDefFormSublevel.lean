import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix in

theorem posDef_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ε * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hx
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x) := by
    apply Continuous.dotProduct continuous_id
    exact Continuous.matrix_mulVec continuous_const continuous_id
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere _ _
  have key : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, ε ≤ x ⬝ᵥ (A *ᵥ x) := by
    rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos x0 ?_, fun x hx => hmin hx⟩
      rintro rfl
      simp at hx0
  obtain ⟨ε, hε, hb⟩ := key
  refine ⟨ε, hε, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hb _ hu
  have e : (‖x‖⁻¹ • x) ⬝ᵥ (A *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [sq, mul_assoc]
  rw [e] at h1
  have h2 : 0 < ‖x‖ ^ 2 := by positivity
  calc ε * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x))) * ‖x‖ ^ 2 := by gcongr
    _ = x ⬝ᵥ (A *ᵥ x) := by field_simp

open Matrix in

theorem sublevel_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) →
    ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  intro X _ _ _ β hsym hpos c
  obtain ⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ X) :=
    ⟨_, ⟨Module.finBasis ℤ X⟩⟩
  obtain ⟨b⟩ := b
  let Q : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => ((β (b i) (b j) : ℤ) : ℚ)
  have hQs : Q.IsSymm := by
    ext i j
    simp [Q, hsym (b i) (b j)]
  have hval : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i)
      = ∑ i, ∑ j, β (b i) (b j) * v i * v j := by
    intro v
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hne : ∀ v : Fin n → ℤ, v ≠ 0 → (∑ i, v i • b i) ≠ 0 := by
    intro v hv h0
    exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h0))
  have hQpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := by
    intro v hv
    have h := hpos _ (hne v hv)
    rw [hval] at h
    have h' : (0 : ℚ) < ((∑ i, ∑ j, β (b i) (b j) * v i * v j : ℤ) : ℚ) := by exact_mod_cast h
    simpa [Q] using h'
  have hA := GlobalTheory.CompanionTheory.Ar.Fan.posDef_of_int_pos n Q hQs hQpos
  obtain ⟨ε, hε, hco⟩ := posDef_coercive _ hA
  obtain ⟨N, hN⟩ := exists_nat_ge ((c : ℝ) / ε)
  have hbound : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i) ≤ c →
      ∀ i, |v i| ≤ (N + 1 : ℤ) := by
    intro v hv i
    have h1 := hco (fun i => (v i : ℝ))
    have h2 : (fun i => (v i : ℝ)) ⬝ᵥ ((Q.map (Rat.cast : ℚ → ℝ)) *ᵥ (fun i => (v i : ℝ)))
        = ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) := by
      rw [hval]
      simp only [dotProduct, mulVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Q]
      ring
    rw [h2] at h1
    have h3 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) ≤ c := by exact_mod_cast hv
    have h4 : ‖(fun i => (v i : ℝ))‖ ^ 2 ≤ N := by
      refine le_trans ?_ hN
      rw [le_div_iff₀ hε]
      linarith
    have h5 : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖ := by
      simpa using norm_le_pi_norm (fun i => (v i : ℝ)) i
    have h6 : |(v i : ℝ)| ≤ (N : ℝ) + 1 := by
      nlinarith [sq_nonneg (‖(fun i => (v i : ℝ))‖ - 1), norm_nonneg (fun i => (v i : ℝ))]
    exact_mod_cast h6
  have hfin : (Set.Icc (fun _ : Fin n => -(N + 1 : ℤ)) (fun _ => (N + 1 : ℤ))).Finite :=
    Set.finite_Icc _ _
  refine (hfin.image fun v => ∑ i, v i • b i).subset ?_
  intro y hy
  have hy' : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
  refine ⟨fun i => b.repr y i, ?_, hy'.symm⟩
  have hb2 := hbound (fun i => b.repr y i) (by rw [← hy']; exact hy)
  exact ⟨fun i => (abs_le.1 (hb2 i)).1, fun i => (abs_le.1 (hb2 i)).2⟩

end GlobalTheory.CompanionTheory.Ar.Fan
