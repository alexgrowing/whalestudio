import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.Up_operator_maps_lattice_of_control_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (Λ Λ' : Submodule O Ω), (∀ a ∈ maximalIdeal O, ∀ w ∈ Λ, a • w ∈ Λ') → ∀ F ∈ X.Lat m W Λ, (∀ g i, X.ctrl m W F g i ∈ Λ') → X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W Λ' := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m Λ Λ' h F hF hc
  have hu : ∀ i g k, X.unt m W F i g k ∈ Λ := (Frame.mem_lat X m W Λ F).mp hF
  have hu0 : ∀ i g, X.unt m W F i g 0 ∈ Λ' := fun i g => by
    rw [← Frame.ctrl_apply]
    exact hc g i
  have hF' : ∀ i g, F i g = (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ X.unt m W F i g := fun i g => by
    rw [Frame.unt_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hM : ∀ (M : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω),
      (∀ k l, M k l ∈ (algebraMap O Ω).range) → ∀ w : Fin (W.d + 1) → Ω, (∀ l, w l ∈ Λ') →
      ∀ k, (M *ᵥ w) k ∈ Λ' := by
    intro M hMi w hw k
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun l _ => ?_
    obtain ⟨y, hy⟩ := hMi k l
    rw [← hy, ← Algebra.smul_def]
    exact Λ'.smul_mem y (hw l)
  have main : ∀ c : Ω, (∀ l j, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j ∈ (algebraMap O Ω).range) →
      (∀ l j, j ≠ 0 → ∃ x ∈ maximalIdeal O, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j = algebraMap O Ω x) →
      (c • ∑ᶠ (q : ↥X.I.N ⧸ (X.I.Nconj X.I.z).subgroupOf X.I.N),
        X.rpF Ω (W.d + 1) m (↑(Quotient.out q) * X.I.z)) F ∈ X.Lat m W Λ' := by
    intro c hP hN
    refine finsum_induction (p := fun T : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) => (c • T) F ∈ X.Lat m W Λ') ?_ ?_ ?_
    · simp
    · intro S T hS hT
      simpa [smul_add] using add_mem hS hT
    · intro q
      have hn : ((Quotient.out q : ↥X.I.N) : Gp) ∈ X.I.N := (Quotient.out q).2
      generalize ((Quotient.out q : ↥X.I.N) : Gp) = n at hn ⊢
      rw [Frame.mem_lat]
      intro i g k
      have e : X.unt m W ((c • X.rpF Ω (W.d + 1) m (n * X.I.z)) F) i g
          = (W.ξ n : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ ((c • (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)) *ᵥ
              X.unt m W F i (g * (1, n * X.I.z))) := by
        have e1 : X.rpF Ω (W.d + 1) m (n * X.I.z) F i g = F i (g * (1, n * X.I.z)) := by
          simp [Frame.rpF, Frame.rp, rtr]
        rw [Frame.unt_apply, LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, e1,
          hF' i (g * (1, n * X.I.z))]
        simp only [Prod.snd_mul, mul_one, map_mul, Units.val_mul, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec, ← mul_assoc]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, Matrix.mul_smul, Matrix.smul_mulVec]
      rw [e]
      refine hM _ (fun k l => W.int_N _ hn k l) _ (fun l => ?_) k
      simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j = 0
      · subst hj
        obtain ⟨y, hy⟩ := hP l 0
        rw [← hy, ← Algebra.smul_def]
        exact Λ'.smul_mem y (hu0 _ _)
      · obtain ⟨x, hx, hxe⟩ := hN l j hj
        rw [hxe, ← Algebra.smul_def]
        exact h x hx _ (hu _ _ _)
  exact main _ (fun l j => W.int_P _ X.I.z_mem l j) (fun l j hj => W.nilpotent_central_action l j hj)
