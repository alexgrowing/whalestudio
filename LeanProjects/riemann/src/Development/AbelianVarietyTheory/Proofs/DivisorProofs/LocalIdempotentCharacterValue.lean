import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl F) (a : AE F E) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) {a : AE F E}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl F} {u : Matrix m n (AE F E)} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

theorem smul_eq_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) {m n : Type}
    {u : Matrix m n (AE F E)} (hu : At (evFin F v) u) (g : AE F E)
    (h1 : ∀ i j, piW t g * piW t (u i j) = 0) (h2 : ∀ i j, piW (t.comp σ) g * piW (t.comp σ) (u i j) = 0) :
    g • u = 0 := by
  have h0 := one_sub_smul hu
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  ext i j
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u i j = u i j := (congrFun (congrFun h0 i) j).symm
  refine eq_zero_of_piW h t ?_ ?_ ?_
  · rw [Matrix.smul_apply, smul_comm, h3]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h2]

theorem swap_at_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (AE F E)) (v : Pl F) (t : E →ₐ[F] Fv F v) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (AE F E)), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  intro F E _ _ _ _ _ σ h a' d J v t f hf _ _ ht htσ w hw
  refine ⟨?_, ?_⟩
  · intro r hr
    have h1 : r * GlobalTheory.LatVac.liftV v (1 : Fv F v) = 0 := GlobalTheory.LatVac.at_liftV v 1 r hr
    have h2 : r • f = 0 := by rw [← hf, smul_smul, h1, zero_smul]
    have h3 : r * (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = r := by rw [mul_sub, h1, mul_one, sub_zero]
    rw [hw, smul_sub, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, smul_smul, h3,
      ← smul_assoc, h2, zero_smul, smul_zero, sub_self]
  · intro u₁ u₂ hu₁ hu₂
    have hact : actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (f • u₂) (f • u₁) := by
      unfold actB
      rw [hw, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, one_sub_smul hu₁,
        one_sub_smul hu₂, zero_add, add_zero]
    have hneg : ∀ u : Matrix (Fin d) (Fin a') (AE F E), At (evFin F v) u → u.map (piW t) = 0 → f • u = -u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f + 1)
        (fun i j => by rw [show piW t (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
        (fun i j => by rw [map_add, htσ, map_one, neg_add_cancel, zero_mul])
      rwa [add_smul, one_smul, add_eq_zero_iff_eq_neg] at this
    have hpos : ∀ u : Matrix (Fin d) (Fin a') (AE F E), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → f • u = u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f - 1)
        (fun i j => by rw [map_sub, ht, map_one, sub_self, zero_mul])
        (fun i j => by rw [show piW (t.comp σ) (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    exact ⟨fun h1 h2 => by rw [hact, hneg _ hu₁ h1, hneg _ hu₂ h2],
      fun h1 h2 => by rw [hact, hpos _ hu₁ h1, hpos _ hu₂ h2]⟩

end GlobalTheory.SwapAtPlace
