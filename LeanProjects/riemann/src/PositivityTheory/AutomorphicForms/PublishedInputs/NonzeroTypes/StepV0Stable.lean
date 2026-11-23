import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace P_V0stable

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem alg_inj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coe_map_apply {n : ℕ} (A : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    ((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) A : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i j = algebraMap 𝒪[k] k ((A : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := rfl

theorem conj_mem_KC {n r : ℕ} (g u : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) (hu : u ∈ KC k n r) :
    g⁻¹ * u * g ∈ KC k n r := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨⟨B, rfl⟩, hB⟩ := hu
  have hB' : ∀ i j, (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hB i j
    have hyeq : y = (B : Matrix (Fin n) (Fin n) 𝒪[k]) i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j := by
      apply alg_inj
      rw [hyx, coe_map_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    exact hyeq ▸ hy
  have key : ∀ i j, ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j
      - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ 𝓂[k] ^ r := by
    intro i j
    have h : ((A⁻¹ * B * A : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) - 1
        = ((A⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k])
          * ((B : Matrix (Fin n) (Fin n) 𝒪[k]) - 1) * (A : Matrix (Fin n) (Fin n) 𝒪[k]) := by
      rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
    rw [← Matrix.sub_apply, h, Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ ?_
    rw [Matrix.sub_apply]
    exact hB' m l
  rw [← map_inv, ← map_mul, ← map_mul]
  refine ⟨⟨_, rfl⟩, fun i j => ⟨_, key i j, ?_⟩⟩
  rw [coe_map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

end P_V0stable

theorem step_V0stable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : FixedSubspaceStableProp G := by
  intro _ _ g φ hφ
  obtain ⟨h1, h2⟩ : (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO → ∀ x, φ (p * x) = G.lam p * φ x) ∧
      ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev → φ (x * u) = φ x := hφ
  show (∀ p : ↥(KO k (Fin n)), (p : GL (Fin n) k) ∈ G.PO →
      ∀ x, Rreg (k := k) (n := n) g φ (p * x) = G.lam p * Rreg (k := k) (n := n) g φ x) ∧
    ∀ x (u : ↥(KO k (Fin n))), (u : GL (Fin n) k) ∈ KC k n G.lev →
      Rreg (k := k) (n := n) g φ (x * u) = Rreg (k := k) (n := n) g φ x
  refine ⟨fun p hp x => ?_, fun x u hu => ?_⟩
  · show φ (p * x * g) = G.lam p * φ (x * g)
    rw [mul_assoc]
    exact h1 p hp (x * g)
  · show φ (x * u * g) = φ (x * g)
    have hc : ((g⁻¹ * u * g : ↥(KO k (Fin n))) : GL (Fin n) k) ∈ KC k n G.lev := by
      change ((g : GL (Fin n) k))⁻¹ * (u : GL (Fin n) k) * (g : GL (Fin n) k) ∈ KC k n G.lev
      exact P_V0stable.conj_mem_KC _ _ g.2 hu
    have e : x * u * g = x * g * (g⁻¹ * u * g) := by group
    rw [e]
    exact h2 _ _ hc

end Grp

end UpperTheory.TNZ
