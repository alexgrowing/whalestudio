import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsLinSpec

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_LR (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det)
    (Y W : Ix r → O) (hY : ∀ j, Y (Sum.inr j) = 0) (hW : ∀ j, W (Sum.inl j) = 0) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
        T * cG O cj Z T T' Y (Sum.inl (Fin.last r)) *
          cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  set G := gramC cj (Z.map O.subtype) T T' with hGdef
  set c := cG O cj Z T T' Y with hcdef
  have hvm : Matrix.vecMul c G = fun j => (↑(Y j) : E) := by
    rw [hcdef]
    unfold cG
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  have hrel : ∀ j, (↑(Y j) : E) = ∑ i, c i * G i j := by
    intro j
    rw [← congrFun hvm j]
    rfl
  rw [formC_of_rel O cj (Z.map O.subtype) T T' hG Y W c hrel, Fintype.sum_sum_type]
  simp only [hW, ZeroMemClass.coe_zero, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
  have hZ : ∀ j, ∑ b, (Z.map O.subtype) j b * c (Sum.inr b) =
      ↑(Y (Sum.inl j)) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
    intro j
    rw [hrel (Sum.inl j), Fintype.sum_sum_type]
    simp only [hGdef, gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply,
      Matrix.of_apply]
    by_cases hj : j = Fin.last r
    · subst hj
      simp [mul_comm]
    · simp [hj, mul_comm]
  have hcR : (fun b => c (Sum.inr b)) = Matrix.mulVec (Z.map O.subtype)⁻¹
      (fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0) := by
    have hv : Matrix.mulVec (Z.map O.subtype) (fun b => c (Sum.inr b)) =
        fun j => (↑(Y (Sum.inl j)) : E) + if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0 := by
      funext j
      exact hZ j
    rw [← hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hcb : ∀ b, c (Sum.inr b) = Matrix.mulVec (Z.map O.subtype)⁻¹ (fun j => (↑(Y (Sum.inl j)) : E)) b +
      T * c (Sum.inl (Fin.last r)) * (Z.map O.subtype)⁻¹ b (Fin.last r) := by
    intro b
    have h := congrFun hcR b
    rw [h]
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  simp only [hcb, bRaw, lamStarC, map_sum, map_mul, hcj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem fwd_B (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O) (t t' : O)
    (hcT : cj (t : E) = t) (hcT' : cj (t' : E) = t') {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ : kap O Z₂ = kap O Z₁)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) t t').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) t t').det)
    (θ : DDc O cj (Z₁.map O.subtype) t t' ≃ₗ[O] DDc O cj (Z₂.map O.subtype) t t')
    (hθ : θ ∈ ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) t t')
    (γ : MbMod Z₁ →ₗ[O] MbMod Z₂) (γs : MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂))
    (hγ : ∀ m, θ (iL O cj hO Z₁ t t' m) = iL O cj hO Z₂ t t' (γ m))
    (hγs : ∀ m, θ (iR O cj hO Z₁ t t' m) = iR O cj hO Z₂ t t' (γs m))
    (hl : ∀ m, lamLQ O Z₂ hu₂ (γ m) = lamLQ O Z₁ hu₁ m)
    (hls : ∀ m, lamSQ O cj hO Z₂ hu₂ (γs m) = lamSQ O cj hO Z₁ hu₁ m) :
    ∀ y y' y₂ y₂' : Fin (r + 1) → O, γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      γs (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O := by
  intro y y' y₂ y₂' h1 h2
  have e1 : θ (Submodule.Quotient.mk (Sum.elim y 0)) = Submodule.Quotient.mk (Sum.elim y₂ 0) := by
    rw [← iL_mk O cj hO Z₁ t t' y, hγ, h1, iL_mk]
  have e2 : θ (Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y')) =
      Submodule.Quotient.mk (Sum.elim (0 : Fin (r + 1) → O) y₂') := by
    rw [← iR_mk O cj hO Z₁ t t' y', hγs, h2, iR_mk]
  have key := hθ.1 _ _ _ _ e1 e2
  have hly : lamC (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inl j) : E)) =
      lamC (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inl j) : E)) := by
    have := hl (Submodule.Quotient.mk y)
    rw [h1, lamLQ_mk, lamLQ_mk] at this
    exact this
  have hly' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim y₂ 0 : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim y 0 : Ix r → O) (Sum.inr j) : E)) := by
    simp [lamStarC]
  have hls' : lamStarC cj (Z₂.map O.subtype) (fun j => ((Sum.elim 0 y₂' : Ix r → O) (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => ((Sum.elim 0 y' : Ix r → O) (Sum.inr j) : E)) := by
    have := hls (Submodule.Quotient.mk y')
    rw [h2, lamSQ_mk, lamSQ_mk] at this
    exact this
  obtain ⟨c1, -⟩ := cG_transfer O cj hcj Z₁ Z₂ hu₁ hu₂ t t' hG₁ hG₂ hκ _ _ hly hly'
  rw [formC_LR O cj hcj Z₂ hu₂ t t' hG₂ _ _ (fun j => rfl) (fun j => rfl),
    formC_LR O cj hcj Z₁ hu₁ t t' hG₁ _ _ (fun j => rfl) (fun j => rfl), c1, hls',
    add_sub_add_right_eq_sub] at key
  exact key

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
