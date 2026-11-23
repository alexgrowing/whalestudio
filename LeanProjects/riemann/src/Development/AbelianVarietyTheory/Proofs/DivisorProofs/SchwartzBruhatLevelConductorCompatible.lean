import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.PureFix

theorem pureA_fixed : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (m₁ M m₃ : ℕ), 0 < m₁ → 0 < M → 0 < m₃ → (∀ a : κ → AF F, IsMulInt F m₁ a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x) → (∀ x : κ → AF F, g (fun i => (x i).2) ≠ 0 → ∀ i v, ‖(M : Fv F v) * evFin F v (x i)‖ ≤ 1) → (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m₃ : Fv F v)‖) → ψ t = 1) → ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ, ∀ a b : κ → AF F, IsMulInt F (2 * m₁ * M * m₃) a → IsMulInt F (2 * m₁ * M * m₃) b → schr ψ (a, b) (pureA F f g) = pureA F f g := by
  intro F _ _ κ _ ψ g m₁ M m₃ hm₁ hM hm₃ hg hx hψ f a b ha hb
  funext x
  have ha' : IsMulInt F m₁ a := by
    have e : 2 * m₁ * M * m₃ = (2 * M * m₃) * m₁ := by ring
    rw [e] at ha; exact ha.mono
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + a) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i; congr 1; show (x i).1 + (a i).1 = (x i).1; rw [ha.1 i, add_zero]
  have e2 : (fun i => ((x + a) i).2) = (fun i => (x i).2) + fun i => (a i).2 := rfl
  simp only [schr, pureA]
  rw [e1, e2, hg a ha' (fun i => (x i).2)]
  by_cases h0 : g (fun i => (x i).2) = 0
  · simp [h0]
  · have hs : ∀ (c d : κ → AF F), (∀ i, (d i).1 = 0) → (c ⬝ᵥ d).1 = 0 := by
      intro c d hd
      change fstA F (∑ i, c i * d i) = 0
      rw [map_sum]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul]; change (c i).1 * (d i).1 = 0; rw [hd i, mul_zero]
    have hnat : ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), ‖(n : Fv F v)‖ ≤ 1 :=
      fun v n => GlobalTheory.SmoothForms.denom_norm_natCast_le_one v n
    rw [hψ _ ?_ ?_, one_mul]
    · change (x ⬝ᵥ b).1 + (⅟2 : AF F).1 * (a ⬝ᵥ b).1 = 0
      rw [hs x b hb.1, hs a b hb.1, mul_zero, add_zero]
    · intro v
      have hb' : ∀ i, ‖evFin F v (b i)‖ ≤ ‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
        intro i; have := hb.2 v i; push_cast at this; simpa [norm_mul, mul_assoc] using this
      have h2 : ‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖ = 1 := by
        rw [← norm_mul, show (2 : Fv F v) = evFin F v (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul,
          invOf_mul_self, map_one, norm_one]
      have ha2 : ∀ i, ‖evFin F v (⅟2 * a i)‖ ≤ 1 := by
        intro i
        have := ha.2 v i
        push_cast at this
        rw [map_mul, norm_mul]
        calc ‖evFin F v (⅟2 : AF F)‖ * ‖evFin F v (a i)‖
            ≤ ‖evFin F v (⅟2 : AF F)‖ * ‖(2 * m₁ * M * m₃ : Fv F v)‖ := by gcongr
          _ = (‖evFin F v (⅟2 : AF F)‖ * ‖(2 : Fv F v)‖) * ‖((m₁ * M * m₃ : ℕ) : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 := by rw [h2, one_mul]; exact hnat v _
      rw [map_add, dotProduct, dotProduct, Finset.mul_sum, map_sum, map_sum]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [map_mul, norm_mul]
        calc ‖evFin F v (x i)‖ * ‖evFin F v (b i)‖
            ≤ ‖evFin F v (x i)‖ * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr; exact hb' i
          _ = ‖(M : Fv F v) * evFin F v (x i)‖ * ‖((2 * m₁ : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by
              push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * 1 * ‖(m₃ : Fv F v)‖ := by
              gcongr
              · exact hx x h0 i v
              · exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := by ring
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
        rw [← mul_assoc, map_mul, norm_mul]
        calc ‖evFin F v (⅟2 * a i)‖ * ‖evFin F v (b i)‖
            ≤ 1 * (‖(2 * m₁ : Fv F v)‖ * ‖(M : Fv F v)‖ * ‖(m₃ : Fv F v)‖) := by
              gcongr
              · exact ha2 i
              · exact hb' i
          _ = ‖((2 * m₁ * M : ℕ) : Fv F v)‖ * ‖(m₃ : Fv F v)‖ := by push_cast; simp only [norm_mul]; ring
          _ ≤ 1 * ‖(m₃ : Fv F v)‖ := by gcongr; exact hnat v _
          _ = ‖(m₃ : Fv F v)‖ := one_mul _

end GlobalTheory.PureFix

end
