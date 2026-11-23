import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeLocal

section
variable (F : Type) [Field F] [NumberField F]

theorem ev_self (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 := by
  classical
  show (singleV F v 1 : Af F) v = 1
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v 1

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 := by
  classical
  show (singleV F v 1 : Af F) w = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ 1 h

theorem af_ext {α β : Af F} (h : ∀ w, evalV F w α = evalV F w β) : α = β := by
  apply RestrictedProduct.ext
  intro w
  exact h w

end

variable {D : D7}

theorem idem_inl_mul (v : FinPl D) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inl v) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] m := by
  have key : pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) := Prod.ext (mul_zero _) rfl
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, key]

theorem idem_inr_mul (τ : D.what₂.Tau) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inr τ) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = 0 := by
  have key : pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0 * pairA D.host.F 0 α = 0 :=
    Prod.ext (mul_zero _) (zero_mul _)
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, key, TensorProduct.zero_tmul]

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  ext i j
  simp [wAt, mul_add]

theorem wAt_neg {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (-x) = -wAt p x := by
  ext i j
  simp [wAt]

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  ext i j
  simp [wAt]

theorem wAt_mem_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  intro D S T ΛS ΛT P u hu p
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, hw⟩ := hw

    obtain ⟨X, hX⟩ : ∃ X : Fin T.rank → Fin S.rank → D.host.E,
        X = fun i j => a * t i * ∑ k, star (s k) * S.gram k j := ⟨_, rfl⟩

    have gen : ∀ (Q : FinPl D → Prop) (β : Af D.host.F), β ∈ intAf D.host.F →
        (∀ v, ¬ Q v → evalV D.host.F v β = 0) →
        (Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] X i j) ∈ latO S T ΛS ΛT Q := by
      intro Q β hβ hQ
      unfold latO
      refine AddSubgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq]
      exact ⟨β, hβ, hQ, a, ha, s, hs, t, ht, by subst hX; rfl⟩
    have hw' : w = Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j := by
      subst hX
      exact hw
    subst hw'
    rcases p with v | τ
    ·
      have hs1 : ∀ v', evalV D.host.F v' (singleV D.host.F v 1) ∈ v'.adicCompletionIntegers D.host.F := by
        intro v'
        by_cases h : v' = v
        · rw [h, ev_self]
          exact one_mem _
        · rw [ev_ne _ h]
          exact zero_mem _
      have e1 : wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        ext i j
        simp only [wAt, Matrix.of_apply, idem_inl_mul]
      have e2 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) -
            wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (α - singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        rw [e1]
        ext i j
        simp only [Matrix.sub_apply, Matrix.of_apply, ← TensorProduct.sub_tmul]
        congr 1
        exact Prod.ext (sub_self _) rfl
      refine ⟨?_, ?_, fun hp => ?_⟩
      · rw [e1]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_mul]
          exact mul_mem (hs1 v') (hα v')
        · by_cases h : v' = v
          · rw [h] at hv' ⊢
            have hPv : ¬ P v := fun hP => hv' ⟨hP, rfl⟩
            rw [map_mul, hv v hPv, mul_zero]
          · rw [map_mul, ev_ne _ h, zero_mul]
      · rw [e2]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_sub, map_mul]
          exact sub_mem (hα v') (mul_mem (hs1 v') (hα v'))
        · by_cases h : v' = v
          · rw [h, map_sub, map_mul, ev_self, one_mul, sub_self]
          · have hPv : ¬ P v' := fun hP => hv' ⟨hP, fun e => h (Sum.inl_injective e)⟩
            rw [map_sub, map_mul, hv v' hPv, mul_zero, sub_zero]
      · have hPv : ¬ P v := fun hP => hp v hP rfl
        have h0 : singleV D.host.F v 1 * α = 0 := by
          apply af_ext
          intro v'
          by_cases h : v' = v
          · rw [h, map_mul, hv v hPv, mul_zero, map_zero]
          · rw [map_mul, ev_ne _ h, zero_mul, map_zero]
        rw [e1, h0]
        ext i j
        simp only [Matrix.of_apply, Matrix.zero_apply]
        rw [show pairA D.host.F 0 0 = 0 from Prod.ext rfl rfl, TensorProduct.zero_tmul]
    ·
      have e0 : wAt (.inr τ) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = 0 := by
        ext i j
        simp only [wAt, Matrix.of_apply, Matrix.zero_apply, idem_inr_mul]
      refine ⟨?_, ?_, fun _ => e0⟩
      · rw [e0]
        exact zero_mem _
      · rw [e0, sub_zero]
        exact gen _ _ hα (fun v' hv' => hv v' (fun hP => hv' ⟨hP, Sum.inl_ne_inr⟩))
  | zero =>
    rw [wAt_zero, sub_zero]
    exact ⟨zero_mem _, zero_mem _, fun _ => rfl⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨hx1, hx2, hx3⟩ := ihx
    obtain ⟨hy1, hy2, hy3⟩ := ihy
    rw [wAt_add]
    refine ⟨add_mem hx1 hy1, ?_, fun hp => by rw [hx3 hp, hy3 hp, add_zero]⟩
    rw [add_sub_add_comm]
    exact add_mem hx2 hy2
  | neg x _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [wAt_neg]
    refine ⟨neg_mem h1, ?_, fun hp => by rw [h3 hp, neg_zero]⟩
    rw [neg_sub_neg, ← neg_sub]
    exact neg_mem h2

end GlobalTheory.LatticeLocal
