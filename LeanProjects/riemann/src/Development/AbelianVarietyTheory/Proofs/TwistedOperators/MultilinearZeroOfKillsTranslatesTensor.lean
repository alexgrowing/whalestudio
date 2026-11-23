import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensityStatement
open scoped InnerProductSpace

namespace GlobalTheory.DensityMultiPlace

theorem multilinear_translates_zero : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : MultilinearMap ℂ (fun i => Sm i) ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  intro ι _ H _ _ _ G _ π hu hs Sm hd hinv L C hL n c v hv φ u
  classical
  let w : Fin n → (∀ i, G i) → ∀ i, Sm i :=
    fun j g i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩
  have key : ∀ s : Finset ι, ∀ (g : ∀ i, G i) (u : ∀ i, Sm i),
      ∑ j, c j * (∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) * L (s.piecewise u (w j g)) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro g u
      simpa [w] using hv g
    · intro a s ha ih g u
      have hnorm : ∀ (m : ∀ i, Sm i) (x : Sm a),
          ∏ i, ‖((Function.update m a x) i : H i)‖
            = (∏ i ∈ Finset.univ.erase a, ‖(m i : H i)‖) * ‖x‖ := by
        intro m x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self,
          mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hbd : ∀ j (x : Sm a), ‖L.toLinearMap (s.piecewise u (w j g)) a x‖
          ≤ (C * ∏ i ∈ Finset.univ.erase a, ‖((s.piecewise u (w j g)) i : H i)‖) * ‖x‖ := by
        intro j x
        rw [MultilinearMap.toLinearMap_apply, mul_assoc, ← hnorm]
        exact hL _
      have hden : DenseRange (Sm a).subtypeL := (hd a).denseRange_val
      have hui : IsUniformInducing (Sm a).subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
      let Λ : Fin n → (H a →L[ℂ] ℂ) := fun j =>
        (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) •
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)).extend (Sm a).subtypeL
      have hΛ : ∀ j (x : Sm a), Λ j (x : H a) = (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) *
          L (Function.update (s.piecewise u (w j g)) a x) := by
        intro j x
        have := ContinuousLinearMap.extend_eq
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)) hden hui x
        simp only [Λ, ContinuousLinearMap.smul_apply, smul_eq_mul]
        erw [this]
        rw [LinearMap.mkContinuous_apply, MultilinearMap.toLinearMap_apply]
      have hupd : ∀ j (k : G a), s.piecewise u (w j (Function.update g a k))
          = Function.update (s.piecewise u (w j g)) a ⟨π a k (v j a), hinv a k _ (v j a).2⟩ := by
        intro j k
        funext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.piecewise_eq_of_notMem _ _ _ ha, w]
        · rw [Function.update_of_ne hia]
          by_cases his : i ∈ s
          · simp [Finset.piecewise_eq_of_mem _ _ _ his]
          · simp [Finset.piecewise_eq_of_notMem _ _ _ his, w, Function.update_of_ne hia]
      have hG : ∀ k : G a, ∑ j, Λ j (π a k (v j a)) = 0 := by
        intro k
        have h1 := ih (Function.update g a k) u
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (π a k (v j a) : H a) = ((⟨π a k (v j a), hinv a k _ (v j a).2⟩ : Sm a) : H a) from rfl,
          hΛ, hupd, mul_assoc]
      have h2 := GlobalTheory.T.irreducibleUnitary_vector_density (H a) (G a) (π a) (hu a) (hs a) n (fun j => (v j a : H a)) Λ hG
        (φ a) (u a)
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΛ, Finset.prod_insert ha, Finset.piecewise_insert]
      ring
  have h := key Finset.univ (fun _ => 1) u
  simp only [Finset.piecewise_univ] at h
  rw [Finset.sum_mul]
  rw [← h]

end GlobalTheory.DensityMultiPlace
