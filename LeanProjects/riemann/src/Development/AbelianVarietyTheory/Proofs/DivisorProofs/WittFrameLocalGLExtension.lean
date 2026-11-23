import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.SplitFrameAction

section Pure
variable {K : Type} [Field K] {n : ℕ}

theorem conj_diag_update (B D : GL (Fin n) K) (k : Fin n) (ϖ : K)
    (hD : D.1 = diagonal (Function.update 1 k ϖ)) :
    (B * D * B⁻¹).1 = 1 + (ϖ - 1) • vecMulVec (fun a => B.1 a k) (fun c => (B⁻¹).1 k c) := by
  ext a b
  have hB : ∑ c, B.1 a c * (B⁻¹).1 c b = (1 : Matrix (Fin n) (Fin n) K) a b := by
    rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hd : ∀ c, Function.update (1 : Fin n → K) k ϖ c = 1 + if k = c then ϖ - 1 else 0 := by
    intro c; by_cases h : k = c
    · subst h; simp
    · simp [h, Function.update_of_ne (Ne.symm h)]
  rw [Units.val_mul, Units.val_mul, hD, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, hd]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_one, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [hB]; ring

theorem rank_one_mulVec (s : K) (b l w : Fin n → K) :
    (1 + s • vecMulVec b l) *ᵥ w = w + (s * (l ⬝ᵥ w)) • b := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem rank_one_vecMul (s : K) (b l w : Fin n → K) :
    w ᵥ* (1 + s • vecMulVec b l) = w + (s * (w ⬝ᵥ b)) • l := by
  ext a
  simp only [Matrix.vecMul, dotProduct, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem mulVec_of_unitary (G x : GL (Fin n) K) (M' : Matrix (Fin n) (Fin n) K)
    (hU : M'ᵀ * G.1 * x.1 = G.1) (u : Fin n → K) (a : K) (ha : a ≠ 0)
    (hl : (u ᵥ* G.1) ᵥ* x.1 = a • (u ᵥ* G.1)) : M' *ᵥ u = a⁻¹ • u := by
  have key : ∀ w w' : Fin n → K, w ᵥ* (G.1 * x.1) = w' ᵥ* (G.1 * x.1) → w = w' := by
    intro w w' h
    have := congrArg (fun y => y ᵥ* ((G * x)⁻¹).1) h
    simpa only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] using this
  refine key _ _ ?_
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU,
    Matrix.smul_vecMul, ← Matrix.vecMul_vecMul, hl, smul_smul, inv_mul_cancel₀ ha, one_smul]

end Pure

section Herm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def pair (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (p q : Fin n → E) : E := ∑ a, ∑ c, σ (p a) * J a c * q c

theorem pair_swap (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) (p q : Fin n → E) :
    pair σ J p q = σ (pair σ J q p) := by
  simp only [pair, map_sum, map_mul, cm_conj_conj hcm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hJ.1]; ring

theorem cT_mul_mul_apply (P Q : Matrix (Fin n) (Fin r) E) (j i : Fin r) :
    (Formalism.UG.cT (σ : E →+* E) P * J * Q) j i = pair σ J (fun a => P a j) (fun c => Q c i) := by
  simp only [pair, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  exact Finset.sum_comm

theorem cT_mul_mulVec_apply (P : Matrix (Fin n) (Fin r) E) (z : Fin n → E) (j : Fin r) :
    ((Formalism.UG.cT (σ : E →+* E) P * J) *ᵥ z) j = pair σ J (fun a => P a j) z := by
  simp only [pair, Formalism.UG.cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]
  exact Finset.sum_comm

theorem dot_row (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (q : Fin n → E) :
    (fun c => t ((Formalism.UG.cT (σ : E →+* E) Y * J) i c)) ⬝ᵥ (fun a => t (q a)) = t (pair σ J (fun a => Y a i) q) := by
  simp only [pair, Formalism.UG.cT, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Finset.sum_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]
  exact Finset.sum_comm

theorem dot_conj (t : E →ₐ[F] Fv F v) (p q : Fin n → E) :
    ((fun a => (t.comp σ) (p a)) ᵥ* J.map t) ⬝ᵥ (fun c => t (q c)) = t (pair σ J p q) := by
  simp only [pair, Matrix.vecMul, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
    AlgHom.comp_apply]
  exact Finset.sum_comm

theorem vecMul_conj (t : E →ₐ[F] Fv F v) (Y : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (fun a => (t.comp σ) (Y a i)) ᵥ* J.map t = fun c => t ((Formalism.UG.cT (σ : E →+* E) Y * J) i c) := by
  funext c
  simp only [Formalism.UG.cT, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, AlgHom.comp_apply, AlgHom.coe_toRingHom, RingHom.coe_coe]

theorem col_ext (hcm : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (X : Matrix (Fin n) (Fin r) E) (d : Fin r → Fv F v ⊗[F] E)
    (h1 : ∀ j, M.map (splitProj t) *ᵥ (fun a => t (X a j)) = splitProj t (d j) • fun a => t (X a j))
    (h2 : ∀ j, M.map (splitProj (t.comp σ)) *ᵥ (fun a => (t.comp σ) (X a j)) =
      splitProj (t.comp σ) (d j) • fun a => (t.comp σ) (X a j)) :
    M * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * diagonal d := by
  ext a j
  refine split_ext hcm t ?_ ?_
  · have := congrFun (h1 j) a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, splitProj_inclR]
    rw [this]; ring
  · have := congrFun (h2 j) a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, splitProj_inclR]
    rw [this]; ring

end Herm

open Formalism.UG (cT) in

theorem frame_action_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v)
    (B : GL (Fin n) (Fv F v)), (∀ (j : Fin r) (k : Fin n), (k : ℕ) = j →
      (∀ a, B.1 a k = t (X a j)) ∧ ∀ a, (B⁻¹).1 k a = t ((Formalism.UG.cT (σ : E →+* E) Y * J) j a)) →
    ∀ (i : Fin r) (k : Fin n), (k : ℕ) = i → ∀ (ϖ : Fv F v) (D : GL (Fin n) (Fv F v)), D.1 = Matrix.diagonal (Function.update 1 k ϖ) →
    ∀ e : (Fv F v ⊗[F] E)ˣ, splitProj t (e : Fv F v ⊗[F] E) = ϖ → splitProj (t.comp σ) (e : Fv F v ⊗[F] E) = 1 →
    (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 * X.map (inclR (F := F) (Fv F v)) =
        X.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (e : Fv F v ⊗[F] E)) ∧
      (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 * Y.map (inclR (F := F) (Fv F v)) =
        Y.map (inclR (F := F) (Fv F v)) * Matrix.diagonal (Function.update 1 i (sigR (Fv F v) σ ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 *ᵥ (fun a => inclR (F := F) (Fv F v) (z a)) =
          fun a => inclR (F := F) (Fv F v) (z a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW v t B hB i k hk ϖ D hD e he1 he2
  have hMeq : (matHom _ σ J ((splitEquiv hcm hJ t).symm (B * D * B⁻¹))).1 =
      splitPairMat hcm t (B * D * B⁻¹).1 (dualConj (splitGram hJ t) (B * D * B⁻¹)).1 := by
    rw [splitEquiv_symm_apply, matHom_splitLift]; rfl
  rw [hMeq]
  have hMt := splitPairMat_map hcm t (B * D * B⁻¹).1 (dualConj (splitGram hJ t) (B * D * B⁻¹)).1
  have hMs := splitPairMat_map_comp hcm t (B * D * B⁻¹).1 (dualConj (splitGram hJ t) (B * D * B⁻¹)).1
  have hU : (dualConj (splitGram hJ t) (B * D * B⁻¹)).1ᵀ * (splitGram hJ t).1 * (B * D * B⁻¹).1 =
      (splitGram hJ t).1 := eq_dualConj_iff.1 rfl
  have hrank : (B * D * B⁻¹).1 = 1 + (ϖ - 1) • vecMulVec (fun a => t (X a i))
      (fun c => t ((cT (σ : E →+* E) Y * J) i c)) := by
    rw [conj_diag_update B D k ϖ hD]
    congr 3
    · funext a; exact (hB i k hk).1 a
    · funext a; exact (hB i k hk).2 a
  have hϖ : ϖ ≠ 0 := by rw [← he1]; exact (e.isUnit.map (splitProj t)).ne_zero
  have hpinv : splitProj t ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = ϖ⁻¹ := by rw [map_units_inv, he1]
  have hqinv : splitProj (t.comp σ) ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) = 1 := by
    rw [map_units_inv, he2, inv_one]

  have hXX : ∀ j j', pair σ J (fun a => X a j) (fun c => X c j') = 0 := fun j j' => by
    rw [← cT_mul_mul_apply, hW.xx]; rfl
  have hYY : ∀ j j', pair σ J (fun a => Y a j) (fun c => Y c j') = 0 := fun j j' => by
    rw [← cT_mul_mul_apply, hW.yy]; rfl
  have hXY : ∀ j j', pair σ J (fun a => X a j) (fun c => Y c j') = (1 : Matrix (Fin r) (Fin r) E) j j' := fun j j' => by
    rw [← cT_mul_mul_apply, hW.xy]
  have hYX : ∀ j j', pair σ J (fun a => Y a j) (fun c => X c j') = if j' = j then 1 else 0 := fun j j' => by
    rw [pair_swap hcm hJ, hXY, Matrix.one_apply]; split_ifs <;> simp

  have hfix : ∀ p : Fin n → E, pair σ J p (fun c => X c i) = 0 →
      (dualConj (splitGram hJ t) (B * D * B⁻¹)).1 *ᵥ (fun a => (t.comp σ) (p a)) = fun a => (t.comp σ) (p a) := by
    intro p hp
    rw [mulVec_of_unitary (splitGram hJ t) (B * D * B⁻¹) _ hU _ 1 one_ne_zero ?_, inv_one, one_smul]
    rw [hrank, rank_one_vecMul, splitGram_val, dot_conj, hp, map_zero, mul_zero, zero_smul, add_zero, one_smul]
  refine ⟨?_, ?_, ?_⟩
  · refine col_ext hcm t _ X _ (fun j => ?_) (fun j => ?_)
    · rw [hMt, hrank, rank_one_mulVec, dot_row, hYX]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, he1, if_pos rfl, map_one]
        ext a; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      · rw [Function.update_of_ne hj, Pi.one_apply, map_one, if_neg hj, map_zero, mul_zero, zero_smul,
          add_zero, one_smul]
    · rw [hMs, hfix _ (hXX j i)]
      have : splitProj (t.comp σ) (Function.update (1 : Fin r → Fv F v ⊗[F] E) i (e : Fv F v ⊗[F] E) j) = 1 := by
        by_cases hj : j = i
        · subst hj; rw [Function.update_self, he2]
        · rw [Function.update_of_ne hj, Pi.one_apply, map_one]
      rw [this, one_smul]
  · refine col_ext hcm t _ Y _ (fun j => ?_) (fun j => ?_)
    · rw [hMt, hrank, rank_one_mulVec, dot_row, hYY, map_zero, mul_zero, zero_smul, add_zero]
      have : splitProj t (Function.update (1 : Fin r → Fv F v ⊗[F] E) i
          (sigR (Fv F v) σ ((e⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) j) = 1 := by
        by_cases hj : j = i
        · subst hj; rw [Function.update_self, ← splitProj_comp, hqinv]
        · rw [Function.update_of_ne hj, Pi.one_apply, map_one]
      rw [this, one_smul]
    · rw [hMs]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, splitProj_comp_sigR hcm, hpinv]
        refine mulVec_of_unitary (splitGram hJ t) (B * D * B⁻¹) _ hU _ ϖ hϖ ?_
        rw [hrank, rank_one_vecMul, splitGram_val, dot_conj, hYX, if_pos rfl, map_one, mul_one, vecMul_conj]
        ext a; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      · rw [hfix _ (by rw [hYX, if_neg (Ne.symm hj)]), Function.update_of_ne hj, Pi.one_apply, map_one, one_smul]
  · intro z hz1 hz2
    have hsv : ∀ τ : E →ₐ[F] Fv F v, splitVec τ (fun a => inclR (F := F) (Fv F v) (z a)) = fun a => τ (z a) :=
      fun τ => funext fun a => splitProj_inclR τ (z a)
    refine splitVec_ext hcm t ?_ ?_
    · rw [splitVec_mulVec, hsv, hMt, hrank, rank_one_mulVec, dot_row, ← cT_mul_mulVec_apply, hz2]
      simp
    · rw [splitVec_mulVec, hsv, hMs]
      refine hfix z ?_
      rw [pair_swap hcm hJ, ← cT_mul_mulVec_apply, hz1]
      simp

end GlobalTheory.SplitFrameAction
