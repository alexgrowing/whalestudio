import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem degZero_log_comm : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (u : Fl g → Pt E g → ℂ) (a : Fin g ⊕ Fin g → Pt E g → ℂ), (∀ i, ∀ P ∈ cov U g, u (Pi.single i 1) P = Complex.exp (2 * π * Complex.I * a i P)) → (∀ i, ContinuousOn (a i) (cov U g)) → (∀ b ∈ U, ∃ f : Fl g → (Fin g → ℂ) → ℂ, (∀ l ∈ stdLat g, Differentiable ℂ (f l) ∧ ∀ z, u l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ z, f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = 0) → ∀ i j, ∀ P ∈ cov U g, a i (transl τ (Pi.single j 1) P) + a j P = a j (transl τ (Pi.single i 1) P) + a i P := by
  intro g E _ _ U τ u a ha hac hf i j P hP
  obtain ⟨b, z⟩ := P
  have hb : b ∈ U := (Set.mem_prod.1 hP).1
  obtain ⟨f, hf1, hf2⟩ := hf b hb
  have hstd : ∀ k, (Pi.single k 1 : Fl g) ∈ stdLat g := fun k =>
    Submodule.subset_span ⟨k, by simp [Pi.basisFun_apply]⟩
  have hmaps : Set.MapsTo (fun w : Fin g → ℂ => (b, w)) Set.univ (cov U g) :=
    fun w _ => Set.mem_prod.2 ⟨hb, Set.mem_univ _⟩
  have hdisc : DiscreteTopology (Set.range ((↑) : ℤ → ℂ)) :=
    (Complex.isometry_intCast.isEmbedding.toHomeomorph).symm.isEmbedding.discreteTopology
  have key : ∀ k w, a k (b, w) - f (Pi.single k 1) w = a k (b, z) - f (Pi.single k 1) z := by
    intro k w
    refine isPreconnected_univ.constant_of_mapsTo (T := Set.range ((↑) : ℤ → ℂ)) ⟨hdisc⟩
      (f := fun w => a k (b, w) - f (Pi.single k 1) w) (hc := ?_) (hTm := ?_) (hx := Set.mem_univ w) (hy := Set.mem_univ z)
    · exact ((hac k).comp (continuous_const.prodMk continuous_id).continuousOn hmaps).sub
        (hf1 _ (hstd k)).1.continuous.continuousOn
    · intro w _
      have h2 := (hf1 _ (hstd k)).2 w
      rw [ha k (b, w) (hmaps (Set.mem_univ w))] at h2
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
      refine ⟨n, ?_⟩
      have h0 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ h0
      linear_combination -hn
  simp only [transl]
  have e1 := key i (z + per (τ b) (Pi.single j 1))
  have e2 := key j (z + per (τ b) (Pi.single i 1))
  have h := hf2 _ (hstd i) _ (hstd j) z
  linear_combination e1 - e2 + h

end GlobalTheory
