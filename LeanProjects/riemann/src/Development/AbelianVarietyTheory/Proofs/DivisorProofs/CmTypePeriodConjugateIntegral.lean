import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.LowerOps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem act_of_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {x : K ⊗[O] H}
    (hx : x ∈ eigK ρ σ) (a : orderC c) : (ρ a).baseChange K x = σ a • x :=
  Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)

theorem conj_ofF (a : OF E) :
    IsCMField.complexConj E ((ofF c a : orderC c) : E) = ((ofF c a : orderC c) : E) := by
  show IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a
  rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
  exact IsCMField.complexConj_apply_eq_self E _

theorem bar_ne_self (σ : E →+* K) : bar σ ≠ σ := by
  intro h
  apply IsCMField.complexConj_ne_one E
  ext x
  exact σ.injective (congrArg (fun τ : E →+* K => τ x) h)

theorem inK_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {y : H} (hy : y ∈ eigLat (K := K) ρ σ) :
    inK K H y ∈ eigK ρ σ := hy

theorem ext_of_eigLat [IsDomain O] [IsFractionRing O K] (ρ : orderC c →+* Module.End O H) (D : O) (hD : D ≠ 0)
    (hsum : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ) (S T : Module.End K (K ⊗[O] H))
    (hST : ∀ σ : E →+* K, ∀ y ∈ eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y)) : S = T := by
  have hD' : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
  have hsub : ∀ y ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y) := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem σ y hy => exact hST σ y hy
    | zero => simp
    | add y z _ _ hy hz => simp [map_add, hy, hz]
  have hH : ∀ h : H, S (inK K H h) = T (inK K H h) := by
    intro h
    have h1 : inK (O := O) K H (D • h) = algebraMap O K D • inK (O := O) K H h := by
      rw [map_smul, algebraMap_smul K D (inK K H h)]
    have h2 := hsub _ (hsum h)
    rw [h1, map_smul, map_smul] at h2
    exact smul_right_injective _ hD' h2
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
    have : k ⊗ₜ[O] h = k • inK K H h := by simp [inK, TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, hH]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lower_mem_eigK_bar {I : Type} {φ : I → E →+* K} {ρ : orderC c →+* Module.End O H} {e f : I → H}
    (hG : IsGens φ ρ e f) {i : I} {N : Module.End K (K ⊗[O] H)} (hN : IsLower ρ (φ i) (e i) (f i) N) {y : H}
    (hy : y ∈ eigLat (K := K) ρ (φ i)) : N (inK K H y) ∈ eigK ρ (bar (φ i)) := by
  rw [(hG i).1, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hf : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
    have : f i ∈ eigLat (K := K) ρ (bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact inK_mem_eigK this
  rw [map_smul, LinearMap.map_smul_of_tower, hN.1]
  exact Submodule.smul_of_tower_mem _ r hf

theorem lower_commute_and_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D hD _ I _ φ hφ H _ _ ρ Fil B _ hEig e f hG N hN
  have hsum := hEig.2.2.1.2
  refine ⟨fun i a => ?_, fun i j => ?_⟩
  · show N i * (ρ (ofF c a)).baseChange K = (ρ (ofF c a)).baseChange K * N i
    apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, Module.End.mul_apply, act_of_mem_eigK hx, map_smul]
    by_cases hσ : σ = φ i
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN i) hy
      rw [act_of_mem_eigK hm]
      congr 1
      show _ = φ i (IsCMField.complexConj E ((ofF c a : orderC c) : E))
      rw [conj_ofF]
    · rw [(hN i).2 σ hσ _ hx, smul_zero, map_zero]
  · apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hσ : σ = φ j
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN j) hy
      have hne : bar (φ j) ≠ φ i := by
        intro h
        obtain ⟨k, _, hk⟩ := hφ (bar (φ j))
        have hi := hk i (Or.inl h)
        have hj := hk j (Or.inr rfl)
        subst hi; subst hj
        exact bar_ne_self _ h
      exact (hN i).2 _ hne _ hm
    · rw [(hN j).2 σ hσ _ hx, map_zero]

end GlobalTheory.LowerOps
