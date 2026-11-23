import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

theorem bcLin_sub_smul_apply {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : K →+* ℂ)
    (f : W →ₗ[K] W) (a : K) (v : VC σ W) :
    bcLin σ (f - a • LinearMap.id) v = bcLin σ f v - σ a • v := by
  letI : Algebra K ℂ := σ.toAlgebra
  revert v
  show ∀ v : ℂ ⊗[K] W, LinearMap.baseChange ℂ (f - a • LinearMap.id) v = LinearMap.baseChange ℂ f v - σ a • v
  intro v
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1

theorem bcLin_sum_smul {K W G : Type} [Field K] [AddCommGroup W] [Module K W] [Fintype G] (σ : K →+* ℂ)
    (f : G → W →ₗ[K] W) (a : G → K) :
    bcLin σ (∑ g, a g • f g) = ∑ g, σ (a g) • bcLin σ (f g) := by
  letI : Algebra K ℂ := σ.toAlgebra
  show LinearMap.baseChangeHom K ℂ W W (∑ g, a g • f g) = ∑ g, σ (a g) • LinearMap.baseChange ℂ (f g)
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show LinearMap.baseChange ℂ (a g • f g) = _
  rw [LinearMap.baseChange_smul]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul ℂ (a g)]
  rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

theorem finrank_eig_twBC : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  intro K W G _ _ _ _ _ _ σ ρ0 χ J μ c
  letI : Algebra K ℂ := σ.toAlgebra
  set a : J → W →ₗ[K] W := fun p => ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id with ha
  have hker : ∀ p : J, LinearMap.ker (twBC σ ρ0 χ (p : G) -
      ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) • LinearMap.id) = LinearMap.ker (bcLin σ (a p)) := by
    intro p
    ext v
    have hμ : ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) = σ (μ p) := rfl
    have hu : σ (((χ p)⁻¹ : Kˣ) : K) * σ ((χ p * μ p : Kˣ) : K) = σ (μ p) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_left]
    have hu0 : σ (((χ p)⁻¹ : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ha, bcLin_sub_smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, twBC_apply, LinearMap.smul_apply, hμ, ← hu, ← smul_smul, ← smul_sub, smul_eq_zero,
      or_iff_right hu0]
  have heig : eig (twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) = ⨅ p : J, LinearMap.ker (bcLin σ (a p)) :=
    iInf_congr hker
  have halg : Representation.asAlgebraHom (twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g))) =
      bcLin σ (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) := by
    rw [map_sum, bcLin_sum_smul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.asAlgebraHom_single, twBC_apply, smul_smul, map_mul]
  have hbc := TensorProduct.isBaseChange K W ℂ
  have h1 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) J (TensorProduct.mk K ℂ W 1) hbc a
    (fun p => (bcLin σ (a p) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun p v => complexificationBaseChangeLinear_one_tmul σ (a p) v)
  set b : Option J → W →ₗ[K] W := fun o => o.elim (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) a with hb
  have h2 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) (Option J) (TensorProduct.mk K ℂ W 1) hbc b
    (fun o => (bcLin σ (b o) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun o v => complexificationBaseChangeLinear_one_tmul σ (b o) v)
  rw [iInf_option, iInf_option] at h2
  refine ⟨?_, ?_⟩
  · rw [heig]
    exact h1.1.symm
  · rw [heig, halg, inf_comm]
    conv_rhs => rw [inf_comm]
    exact h2.1.symm

end GlobalTheory.DefRead
