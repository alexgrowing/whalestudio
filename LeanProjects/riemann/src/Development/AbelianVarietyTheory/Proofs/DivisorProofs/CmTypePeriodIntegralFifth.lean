import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.EigenPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem natMul_mem_orderC (c : Ideal (OF E)) (z : 𝓞 E) :
    ((Ideal.absNorm c : ℕ) : E) * (z : E) ∈ orderC c := by
  refine mem_orderC.2 ⟨0, ((Ideal.absNorm c : ℕ) : 𝓞 E) * z, ?_, ?_⟩
  · refine Ideal.mul_mem_right z _ ?_
    have h := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) (Ideal.absNorm_mem c)
    simpa using h
  · simp

theorem exists_sep {K : Type} [Field K] [CharZero K] (c : Ideal (OF E)) (hc : c ≠ ⊥) (σ σ' : E →+* K)
    (h : σ' ≠ bar σ) : ∃ a b : orderC c, (b : E) = IsCMField.complexConj E a ∧ σ a ≠ σ' b := by
  by_contra hn
  push_neg at hn
  have hm : ((Ideal.absNorm c : ℕ) : K) ≠ 0 := by
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.1 hc)
  have hz : ∀ z : 𝓞 E, σ (z : E) = σ' (IsCMField.complexConj E (z : E)) := by
    intro z
    have h1 := hn ⟨_, natMul_mem_orderC c z⟩
      ⟨_, natMul_mem_orderC c (IsCMField.ringOfIntegersComplexConj E z)⟩
      (by simp [IsCMField.coe_ringOfIntegersComplexConj])
    simp only [map_mul, map_natCast, IsCMField.coe_ringOfIntegersComplexConj] at h1
    exact mul_left_cancel₀ hm h1
  have heq : σ = bar σ' := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_
    ext z
    exact hz z
  apply h
  rw [heq]
  ext x
  simp [bar, IsCMField.complexConj_apply_apply]

theorem adj_baseChange {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H]
    [Module O H] (B : LinearMap.BilinForm O H) (f g : Module.End O H) (hfg : ∀ h h', B (f h) h' = B h (g h'))
    (x y : K ⊗[O] H) : B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s h =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t h' => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hfg]

end GlobalTheory.EigenPair

theorem GlobalTheory.EigenPair.pairing_eig_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ σ' hne x hx y hy
  haveI : CharZero K := by
    refine ⟨fun m n hmn => ?_⟩
    rw [← map_natCast (algebraMap O K), ← map_natCast (algebraMap O K) n] at hmn
    exact Nat.cast_injective (IsFractionRing.injective O K hmn)
  obtain ⟨a, b, hab, hsep⟩ := GlobalTheory.EigenPair.exists_sep c hc σ σ' hne
  have hadj := hL.2.2.2.2.2.2.2.2 a b hab
  have hxa : (ρ a).baseChange K x = σ a • x :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)
  have hyb : (ρ b).baseChange K y = σ' b • y :=
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy b)
  have key := GlobalTheory.EigenPair.adj_baseChange B (ρ a) (ρ b) hadj x y
  rw [hxa, hyb, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul] at key
  have h2 : (σ a - σ' b) * B.baseChange K x y = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hsep)
